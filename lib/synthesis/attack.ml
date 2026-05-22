open Language

type result = {
  size : Size.size;
  objective : string;
  witness : Objective.witness;
  tree : BigStep.ctree;
  cmd : Syntax.Cmd.t;
  analysis_aenv : Analyzer.Abs_domain.Abs_env.t;
}

type progress = {
  size : Size.size;
  exps : int;
  cmds : int;
  etrees : int;
  ctrees : int;
  skipped_reason : string option;
}

type analysis_cache =
  (Environment.t * Syntax.Cmd.t, Analyzer.Abs_domain.Abs_env.t) Hashtbl.t

let component_cap = 1000
let default_seed = 42

let create_analysis_cache () =
  Hashtbl.create 1024

let analyze_cmd ?init_cenv cmd =
  Analyzer.Analyzer_engine.analysis ?init_cenv (Syntax.Cmd.dummy_lbl cmd)

let analyze_cmd_cached cache ?(init_cenv = Environment.empty) cmd =
  let key = (init_cenv, cmd) in
  match Hashtbl.find_opt cache key with
  | Some analysis_aenv -> analysis_aenv
  | None ->
      let analysis_aenv = analyze_cmd ~init_cenv cmd in
      Hashtbl.add cache key analysis_aenv;
      analysis_aenv

let starts_from_zero_env cfg ct =
  let init_cenv, _, _ = BigStep.get_c_concl ct in
  List.for_all (fun x -> Environment.lookup x init_cenv = 0) cfg.Config.vars

let check_objectives ~objectives ~cfg ~var ~tree ~cmd ~analysis_aenv =
  objectives
  |> List.find_map (fun objective ->
         match
           objective.Objective.check ~cfg ~var ~tree ~cmd ~analysis_aenv
         with
         | Some witness -> Some (objective.Objective.name, witness)
         | None -> None)

let check_ctree ~cache ~cfg ~var ~objectives size ct =
  let init_cenv, cmd, _ = BigStep.get_c_concl ct in
  if not (starts_from_zero_env cfg ct) then None
  else
    let analysis_aenv = analyze_cmd_cached cache ~init_cenv cmd in
    match
      check_objectives ~objectives ~cfg ~var ~tree:ct ~cmd ~analysis_aenv
    with
    | Some (objective, witness) ->
        Some { size; objective; witness; tree = ct; cmd; analysis_aenv }
    | None -> None

let find_first_in_ctrees ~cache ~cfg ~var ~objectives size tbl =
  Component_set.fold_ctrees size tbl
    (fun ct result ->
      match result with
      | Some _ -> result
      | None -> check_ctree ~cache ~cfg ~var ~objectives size ct)
    None

let find_all_in_ctrees ~cache ~cfg ~var ~objectives size tbl =
  Component_set.fold_ctrees size tbl
    (fun ct results ->
      match check_ctree ~cache ~cfg ~var ~objectives size ct with
      | Some result -> result :: results
      | None -> results)
    []
  |> List.rev

let progress_of_bucket size bucket =
  {
    size;
    exps = Component_set.ExpSet.cardinal bucket.Component_set.exps;
    cmds = Component_set.CmdSet.cardinal bucket.cmds;
    etrees = Component_set.ETreeSet.cardinal bucket.etrees;
    ctrees = Component_set.CTreeSet.cardinal bucket.ctrees;
    skipped_reason = None;
  }

let report_progress on_progress size tbl =
  match on_progress with
  | None -> ()
  | Some f ->
      let bucket = Component_set.get_bucket size tbl in
      f (progress_of_bucket size bucket)

let in_rect_bound bound size =
  Size.prog_size size <= Size.prog_size bound
  && Size.proof_size size <= Size.proof_size bound

let needed_in_bound bound size =
  if Size.proof_size size = 0 then
    in_rect_bound bound (Size.make (Size.prog_size size + 2) 2)
  else in_rect_bound bound size

let report_skipped_progress on_progress size reason =
  match on_progress with
  | None -> ()
  | Some f ->
      f
        {
          size;
          exps = 0;
          cmds = 0;
          etrees = 0;
          ctrees = 0;
          skipped_reason = Some reason;
        }

let diagonal_forever =
  let sizes_at_total total =
    let rec loop prog () =
      if prog < 1 then Seq.Nil
      else
        let proof = total - prog in
        let cur = Size.make prog proof in
        (* Raw syntax components are only needed for unexecuted command
           positions in proof trees. The first such demand for a command of
           prog size k is CWhileFalse at proof target (k + 2, 2), so emit
           (k, 0) immediately before that target instead of eagerly walking
           all syntax-only sizes. *)
        if proof = 2 && prog >= 3 then
          Seq.Cons (Size.make (prog - 2) 0, fun () ->
              Seq.Cons (cur, loop (prog - 1)))
        else Seq.Cons (cur, loop (prog - 1))
    in
    loop (total - 1)
  in
  let rec totals total () =
    Seq.append (sizes_at_total total) (totals (total + 1)) ()
  in
  totals 2

let find_attack ?(seed = default_seed) ?on_progress ~var ~objectives cfg =
  Random.init seed;
  let cache = create_analysis_cache () in
  let rec loop tbl sizes =
    match sizes () with
    | Seq.Nil -> None
    | Seq.Cons (size, sizes) -> (
        let tbl = Bottom_up.grow_at_size cfg size tbl in
        let tbl = Component_set.cap_size_by_score component_cap size tbl in
        report_progress on_progress size tbl;
        match find_first_in_ctrees ~cache ~cfg ~var ~objectives size tbl with
        | Some result -> Some result
        | None -> loop tbl sizes)
  in
  loop Component_set.empty diagonal_forever

let find_top_attack ?seed ?on_progress ~var cfg =
  find_attack ?seed ?on_progress ~var
    ~objectives:[ Objective.unsound; Objective.top ]
    cfg

let find_all_attacks ?(seed = default_seed) ?on_progress ~var ~objectives cfg
    bound =
  Random.init seed;
  let cache = create_analysis_cache () in
  let rec loop tbl results sizes =
    match sizes () with
    | Seq.Nil -> List.rev results
    | Seq.Cons (size, sizes) ->
        if Size.total size > Size.total bound then List.rev results
        else if not (needed_in_bound bound size) then (
          report_skipped_progress on_progress size
            ("outside rectangular bound=" ^ Size.to_string bound);
          loop tbl results sizes)
        else
          let tbl = Bottom_up.grow_at_size cfg size tbl in
          let tbl = Component_set.cap_size_by_score component_cap size tbl in
          report_progress on_progress size tbl;
          let new_results =
            find_all_in_ctrees ~cache ~cfg ~var ~objectives size tbl
          in
          loop tbl (List.rev_append new_results results) sizes
  in
  loop Component_set.empty [] diagonal_forever

let find_all_top_attacks ?seed ?on_progress ~var cfg bound =
  find_all_attacks ?seed ?on_progress ~var
    ~objectives:[ Objective.unsound; Objective.top ]
    cfg bound
