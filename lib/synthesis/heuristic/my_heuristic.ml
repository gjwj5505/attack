open Language

type t = {
  rng : Random.State.t;
  target_var : string;
  cmd_cache : (string, float) Hashtbl.t;
  exp_cache : (string, float) Hashtbl.t;
}

type state = t

let make ~seed =
  {
    rng = Random.State.make [| seed |];
    target_var = (Config_util.attack ()).Config.target_var;
    cmd_cache = Hashtbl.create 512;
    exp_cache = Hashtbl.create 512;
  }

let score_jitter t = Random.State.float t.rng 0.25

let rec contains_target_var_exp target_var (exp : Syntax.Exp.t) =
  match exp with
  | Syntax.Exp.Int _ -> false
  | Syntax.Exp.Var x -> x = target_var
  | Syntax.Exp.Uop (_, e) -> contains_target_var_exp target_var e
  | Syntax.Exp.Bop (_, e1, e2) ->
      contains_target_var_exp target_var e1 || contains_target_var_exp target_var e2

let bop_bonus : Syntax.Exp.bop -> float = function
  | Syntax.Exp.Eq | Syntax.Exp.Ne | Syntax.Exp.Lt | Syntax.Exp.Gt
  | Syntax.Exp.Le | Syntax.Exp.Ge ->
      1.2
  | Syntax.Exp.Plus | Syntax.Exp.Minus -> 1.4
  | Syntax.Exp.Times -> 2.0

let env_pressure env =
  0.25
  *. Environment.VarMap.fold
       (fun _ cval acc -> acc +. Float.of_int (abs cval))
       env 0.0

let rec struct_exp_score (exp : Syntax.Exp.t) =
  match exp with
  | Syntax.Exp.Int _ -> 0.4
  | Syntax.Exp.Var _ -> 0.8
  | Syntax.Exp.Uop (_, e) -> 1.2 +. struct_exp_score e
  | Syntax.Exp.Bop (op, e1, e2) ->
      bop_bonus op +. struct_exp_score e1 +. struct_exp_score e2

let key_cmd (cmd : Syntax.Cmd.t) = Syntax.Cmd.string_of_t cmd

let key_env (env : Environment.t) = Environment.string_of_env env

let cache_lookup (cache : (string, float) Hashtbl.t) (k : string) =
  try Some (Hashtbl.find cache k) with Not_found -> None

let analyzer_value_score (value : Analyzer.aval) =
  let base =
    if Analyzer.is_top value then 5.0
    else if Analyzer.is_unbounded value then 3.2
    else if Analyzer.is_singleton 0 value then 2.5
    else 1.2
  in
  if Analyzer.contains_concrete 0 value then base +. 0.7 else base

let analyze_cmd_score (state : state) (init_cenv : Environment.t) (cmd : Syntax.Cmd.t)
    : float =
  let key = key_env init_cenv ^ "||" ^ key_cmd cmd in
  match cache_lookup state.cmd_cache key with
  | Some s -> s
  | None ->
      let score =
        try
          let aenv =
            Analyzer.analysis Analyzer.default ~init_cenv (Syntax.Cmd.dummy_lbl cmd)
          in
          analyzer_value_score (Analyzer.find state.target_var aenv)
        with _ -> 0.0
      in
      Hashtbl.replace state.cmd_cache key score;
      score

let analyze_exp_score (state : state) (init_cenv : Environment.t) (exp : Syntax.Exp.t)
    : float =
  let key = key_env init_cenv ^ "||" ^ Syntax.Exp.string_of_t exp in
  match cache_lookup state.exp_cache key with
  | Some s -> s
  | None ->
      let score =
        try analyze_cmd_score state init_cenv (Syntax.Cmd.Assign (state.target_var, exp))
        with _ -> 0.0
      in
      Hashtbl.replace state.exp_cache key score;
      score

let score_exp (state : state) (exp : Syntax.Exp.t) =
  let structural = struct_exp_score exp in
  let target_bonus = if contains_target_var_exp state.target_var exp then 2.0 else 0.0 in
  let size_bonus = 0.25 *. Float.of_int (Size.sizeof_Exp exp) in
  let analysis_bonus = 0.8 *. analyze_exp_score state Environment.empty exp in
  structural +. target_bonus +. size_bonus +. analysis_bonus +. score_jitter state

let rec score_cmd_internal (state : state) (cmd : Syntax.Cmd.t) =
  match cmd with
  | Syntax.Cmd.Assign (id, exp) ->
      let id_bonus = if id = state.target_var then 1.5 else 0.3 in
      1.0 +. id_bonus +. score_exp state exp
  | Syntax.Cmd.Seq ({ cmd = c1; _ }, { cmd = c2; _ }) ->
      0.8 +. score_cmd_internal state c1 +. score_cmd_internal state c2
  | Syntax.Cmd.If (pred, { cmd = c1; _ }, { cmd = c2; _ }) ->
      2.0 +. score_exp state pred +. score_cmd_internal state c1
      +. score_cmd_internal state c2
  | Syntax.Cmd.While (pred, { cmd = cbody; _ }) ->
      2.5 +. score_exp state pred +. score_cmd_internal state cbody

let score_cmd (state : state) (cmd : Syntax.Cmd.t) =
  score_cmd_internal state cmd
  +. analyze_cmd_score state Environment.empty cmd
  +. score_jitter state

let score_etree (state : state) (etree : BigStep.etree) =
  let rec aux (et : BigStep.etree) =
    match et with
    | BigStep.EInt (_, (cenv, exp, _)) ->
        let analysis_bonus = 0.6 *. analyze_exp_score state cenv exp in
        0.6 +. score_exp state exp +. env_pressure cenv +. analysis_bonus
    | BigStep.EVar (_, (cenv, exp, _)) ->
        let analysis_bonus = 0.6 *. analyze_exp_score state cenv exp in
        1.1 +. score_exp state exp +. env_pressure cenv +. 0.9 +. analysis_bonus
    | BigStep.EUop (sub, (cenv, exp, _)) ->
        let analysis_bonus = 0.6 *. analyze_exp_score state cenv exp in
        1.6 +. score_exp state exp +. env_pressure cenv +. aux sub
        +. analysis_bonus
    | BigStep.EBop ((left, right), (cenv, exp, _)) ->
        let analysis_bonus = 0.6 *. analyze_exp_score state cenv exp in
        1.9 +. score_exp state exp +. env_pressure cenv +. aux left +. aux right
        +. analysis_bonus
  in
  aux etree +. score_jitter state

let rec score_ctree (state : state) (ctree : BigStep.ctree) =
  match ctree with
  | BigStep.CAssign (etree, (cenv0, cmd, cenv1)) ->
      let conclusion_score = env_pressure cenv0 +. env_pressure cenv1 in
      1.5 +. score_etree state etree +. score_cmd state cmd
      +. analyze_cmd_score state cenv0 cmd +. conclusion_score
  | BigStep.CSeq ((ct1, ct2), (cenv0, _cmd, cenv1)) ->
      let conclusion_score = env_pressure cenv0 +. env_pressure cenv1 in
      0.8 +. score_ctree state ct1 +. score_ctree state ct2 +. conclusion_score
  | BigStep.CIfTrue ((etree, ct), (cenv0, _cmd, cenv1)) ->
      2.2 +. score_etree state etree +. score_ctree state ct +. 1.5
      +. env_pressure cenv0 +. env_pressure cenv1
  | BigStep.CIfFalse ((etree, ct), (cenv0, _cmd, cenv1)) ->
      2.2 +. score_etree state etree +. score_ctree state ct +. 1.5
      +. env_pressure cenv0 +. env_pressure cenv1
  | BigStep.CWhileTrue ((etree, body, rest), (cenv0, _cmd, cenv1)) ->
      3.0 +. score_etree state etree +. score_ctree state body
      +. score_ctree state rest +. 1.8 +. env_pressure cenv0 +. env_pressure cenv1
  | BigStep.CWhileFalse (etree, (cenv0, cmd, cenv1)) ->
      1.8 +. score_etree state etree +. 0.7 +. score_cmd state cmd
      +. env_pressure cenv0 +. env_pressure cenv1

let split_at n items =
  let rec aux n acc items =
    if n <= 0 then (List.rev acc, items)
    else
      match items with
      | [] -> (List.rev acc, [])
      | item :: rest -> aux (n - 1) (item :: acc) rest
  in
  aux n [] items

let score_weight (_ : t) score = Float.max 0.0 score +. 1.0

let choose_index_by_weight (t : t) (candidates : ('a * float) list) =
  let total =
    List.fold_left
      (fun acc (_, score) -> acc +. score_weight t score) 0.0 candidates
  in
  if total <= 0.0 then None
  else
    let pick = Random.State.float t.rng total in
    let rec loop acc index = function
      | [] -> None
      | item :: rest ->
          let acc = acc +. score_weight t (snd item) in
          if Float.compare pick acc <= 0 then Some index else loop acc (index + 1) rest
    in
    loop 0.0 0 candidates

let remove_at idx items =
  let rec aux i acc = function
    | [] -> (None, List.rev acc)
    | item :: rest ->
        if i = 0 then (Some item, List.rev_append acc rest)
        else aux (i - 1) (item :: acc) rest
  in
  aux idx [] items

let weighted_sample_without_replacement (t : t) k items =
  let rec aux k candidates acc =
    if k <= 0 || candidates = [] then List.rev acc
    else
      match choose_index_by_weight t candidates with
      | None -> List.rev acc
      | Some idx -> (
          match remove_at idx candidates with
          | None, _ -> List.rev acc
          | Some item, rest -> aux (k - 1) rest (item :: acc))
  in
  aux k items []

let choose_n (_t : t) n items =
  items
  |> List.stable_sort
       (fun (_, left) (_, right) -> Float.compare right left)
  |> fun items -> fst (split_at n items)

let trim (t : t) items =
  let fixed_count = 300 in
  let max_count = 1000 in
  let by_score =
    List.stable_sort
      (fun (_, left) (_, right) -> Float.compare right left)
      items
  in
  let kept_fixed, remaining =
    split_at fixed_count by_score
  in
  let fixed_len = List.length kept_fixed in
  let sample_count = max 0 (min (max_count - fixed_len) (List.length remaining)) in
  let sampled = weighted_sample_without_replacement t sample_count remaining in
  kept_fixed @ sampled

let grow_count = function
  | rule when BigStep.is_ternary_grow_rule rule -> 10
  | _ -> 32

let choose_for_grow t rule items = choose_n t (grow_count rule) items
