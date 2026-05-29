open Language

type result = {
  size : Size.size;
  objective : string;
  witness : Objective.witness;
  tree : BigStep.ctree;
  cmd : Syntax.Cmd.t;
  analysis_aenv : Analyzer.aenv;
}

type progress = {
  size : Size.size;
  exps : int;
  cmds : int;
  etrees : int;
  ctrees : int;
  found : int;
  skipped_reason : string option;
}

type analysis_cache =
  (Environment.t * Syntax.Cmd.t, Analyzer.aenv) Hashtbl.t

let component_cap = 1000
let default_seed = Config.seed

let create_analysis_cache () =
  Hashtbl.create 1024

let analyze_cmd ?(analyzer = Analyzer.default) ?init_cenv cmd =
  Analyzer.analysis analyzer ?init_cenv (Syntax.Cmd.dummy_lbl cmd)

let analyze_cmd_cached cache ?analyzer ?(init_cenv = Environment.empty) cmd =
  let key = (init_cenv, cmd) in
  match Hashtbl.find_opt cache key with
  | Some analysis_aenv -> analysis_aenv
  | None ->
      let analysis_aenv = analyze_cmd ?analyzer ~init_cenv cmd in
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

let check_ctree ~cache ~analyzer ~cfg ~var ~objectives size ct =
  let init_cenv, cmd, _ = BigStep.get_c_concl ct in
  if not (starts_from_zero_env cfg ct) then None
  else
    let analysis_aenv = analyze_cmd_cached cache ~analyzer ~init_cenv cmd in
    match
      check_objectives ~objectives ~cfg ~var ~tree:ct ~cmd ~analysis_aenv
    with
    | Some (objective, witness) ->
        Some { size; objective; witness; tree = ct; cmd; analysis_aenv }
    | None -> None

let find_first_in_ctrees ~cache ~analyzer ~cfg ~var ~objectives size tbl =
  Component_set.fold_ctrees size tbl
    (fun ct result ->
      match result with
      | Some _ -> result
      | None -> check_ctree ~cache ~analyzer ~cfg ~var ~objectives size ct)
    None

let find_all_in_ctrees ~cache ~analyzer ~cfg ~var ~objectives size tbl =
  Component_set.fold_ctrees size tbl
    (fun ct results ->
      match check_ctree ~cache ~analyzer ~cfg ~var ~objectives size ct with
      | Some result -> result :: results
      | None -> results)
    []
  |> List.rev

let progress_of_bucket size found bucket =
  {
    size;
    exps = Component_set.ExpSet.cardinal bucket.Component_set.exps;
    cmds = Component_set.CmdSet.cardinal bucket.cmds;
    etrees = Component_set.ETreeSet.cardinal bucket.etrees;
    ctrees = Component_set.CTreeSet.cardinal bucket.ctrees;
    found;
    skipped_reason = None;
  }

let report_progress on_progress size found tbl =
  match on_progress with
  | None -> ()
  | Some f ->
      let bucket = Component_set.get_bucket size tbl in
      f (progress_of_bucket size found bucket)

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
          found = 0;
          skipped_reason = Some reason;
        }

let search_sizes ?(heuristic = Heuristic.none)
    ?(analyzer = Analyzer.default) ?on_progress ~var ~objectives
    cfg ~init ~stop ~done_ ~skip ~collect ~found_count ~update =
  Heuristic.set heuristic;
  let cache = create_analysis_cache () in
  let rec loop tbl acc sizes =
    match sizes () with
    | Seq.Nil -> acc
    | Seq.Cons (size, sizes) ->
        if done_ acc || stop size then acc
        else
          match skip size with
          | Some reason ->
              report_skipped_progress on_progress size reason;
              loop tbl acc sizes
          | None ->
              let tbl = Bottom_up.grow_at_size cfg size tbl in
              let tbl =
                Component_set.cap_size_by_score component_cap size tbl
              in
              let found =
                collect ~cache ~analyzer ~cfg ~var ~objectives size tbl
              in
              report_progress on_progress size (found_count found) tbl;
              let acc = update acc found in
              loop tbl acc sizes
  in
  loop Component_set.empty init Size_schedule.square_forever

let find_attack ?heuristic ?analyzer ?on_progress ~var ~objectives cfg =
  search_sizes ?heuristic ?analyzer ?on_progress ~var ~objectives cfg ~init:None
    ~stop:(fun _ -> false)
    ~done_:(function Some _ -> true | None -> false)
    ~skip:(fun _ -> None)
    ~collect:find_first_in_ctrees
    ~found_count:(function Some _ -> 1 | None -> 0)
    ~update:(fun result found ->
      match result with
      | Some _ -> result
      | None -> found)

let find_top_attack ?heuristic ?analyzer ?on_progress ~var cfg =
  find_attack ?heuristic ?analyzer ?on_progress ~var
    ~objectives:[ Objective.unsound; Objective.top ]
    cfg

let iter_attacks ?heuristic ?analyzer ?on_progress ~var ~objectives cfg
    ~on_results =
  search_sizes ?heuristic ?analyzer ?on_progress ~var ~objectives cfg ~init:()
    ~stop:(fun _ -> false)
    ~done_:(fun () -> false)
    ~skip:(fun _ -> None)
    ~collect:find_all_in_ctrees
    ~found_count:List.length
    ~update:(fun () results -> on_results results)

let find_all_attacks ?heuristic ?analyzer ?on_progress ~var ~objectives cfg bound =
  search_sizes ?heuristic ?analyzer ?on_progress ~var ~objectives cfg ~init:[]
    ~stop:(fun size -> Size.total size > Size.total bound)
    ~done_:(fun _ -> false)
    ~skip:(fun size ->
      if needed_in_bound bound size then None
      else Some ("outside rectangular bound=" ^ Size.to_string bound))
    ~collect:find_all_in_ctrees
    ~found_count:List.length
    ~update:(fun results found -> List.rev_append found results)
  |> List.rev

let find_all_top_attacks ?heuristic ?analyzer ?on_progress ~var cfg bound =
  find_all_attacks ?heuristic ?analyzer ?on_progress ~var
    ~objectives:[ Objective.unsound; Objective.top ]
    cfg bound
