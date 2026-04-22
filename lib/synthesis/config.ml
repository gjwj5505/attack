open Language

type t = {
  vars : string list;
  ints : int list;
  value_range : int * int;
  uops : Syntax.Exp.uop list;
  bops : Syntax.Exp.bop list;
}

let default_uops = Syntax.Exp.[ Uminus ]

let default_bops =
  Syntax.Exp.
    [
      Lt; Plus; Eq;
      (* Gt; Ne; Le; Ge; Minus; Times *)
    ]

let make ?(uops = default_uops) ?(bops = default_bops) ~vars ~ints ~value_range
    () =
  { vars; ints; value_range; uops; bops }

let attack () =
  make ~vars:[ "x"; "y" ] ~ints:[ -1; 0; 1 ] ~value_range:(0, 4) ()

let values_in_range (lo, hi) =
  if lo > hi then [] else List.init (hi - lo + 1) (fun i -> lo + i)

let valid_env cfg env =
  let lo, hi = cfg.value_range in
  let vars_in_range =
    List.for_all
      (fun x ->
        let v = Environment.lookup x env in
        lo <= v && v <= hi)
      cfg.vars
  in
  let only_config_vars =
    Environment.VarMap.bindings env
    |> List.for_all (fun (x, _) -> List.mem x cfg.vars)
  in
  vars_in_range && only_config_vars

let bounded_envs cfg =
  let values = values_in_range cfg.value_range in
  let rec aux = function
    | [] -> [ Environment.empty ]
    | x :: xs ->
        aux xs
        |> List.concat_map (fun env ->
            List.map (fun v -> Environment.update x v env) values)
  in
  aux cfg.vars

let is_in_bound cfg x =
  let lo, hi = cfg.value_range in
  lo <= x && x <= hi
