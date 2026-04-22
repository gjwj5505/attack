open Language

type result = {
  size : Size.size;
  tree : BigStep.ctree;
  cmd : Syntax.Cmd.t;
  analysis_result : Analyzer.Abs_mem.t;
}

type progress = {
  size : Size.size;
  exps : int;
  cmds : int;
  etrees : int;
  ctrees : int;
}

type analysis_cache = (Syntax.Cmd.t, Analyzer.Abs_mem.t) Hashtbl.t

let create_analysis_cache () =
  Hashtbl.create 1024

let analysis_result_is_top var mem =
  Analyzer.Abs_val.is_top (Analyzer.Abs_mem.find var mem)

let analyze_cmd cmd =
  Analyzer.analysis (Syntax.Cmd.dummy_lbl cmd)

let analyze_cmd_cached cache cmd =
  match Hashtbl.find_opt cache cmd with
  | Some analysis_result -> analysis_result
  | None ->
      let analysis_result = analyze_cmd cmd in
      Hashtbl.add cache cmd analysis_result;
      analysis_result

let check_ctree ~cache ~var size ct =
  let _, cmd, _ = BigStep.get_c_concl ct in
  let analysis_result = analyze_cmd_cached cache cmd in
  if analysis_result_is_top var analysis_result then
    Some { size; tree = ct; cmd; analysis_result }
  else None

let find_first_in_ctrees ~cache ~var size tbl =
  Component_set.CTreeSet.to_seq (Component_set.ctrees_of_size size tbl)
  |> Seq.filter_map (check_ctree ~cache ~var size)
  |> Seq.uncons
  |> Option.map fst

let find_all_in_ctrees ~cache ~var size tbl =
  Component_set.CTreeSet.fold
    (fun ct results ->
      match check_ctree ~cache ~var size ct with
      | Some result -> result :: results
      | None -> results)
    (Component_set.ctrees_of_size size tbl)
    []
  |> List.rev

let progress_of_bucket size bucket =
  {
    size;
    exps = Component_set.ExpSet.cardinal bucket.Component_set.exps;
    cmds = Component_set.CmdSet.cardinal bucket.cmds;
    etrees = Component_set.ETreeSet.cardinal bucket.etrees;
    ctrees = Component_set.CTreeSet.cardinal bucket.ctrees;
  }

let report_progress on_progress size tbl =
  match on_progress with
  | None -> ()
  | Some f ->
      let bucket = Component_set.get_bucket size tbl in
      f (progress_of_bucket size bucket)

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

let find_top_attack ?on_progress ~var cfg =
  let cache = create_analysis_cache () in
  let rec loop tbl sizes =
    match sizes () with
    | Seq.Nil -> None
    | Seq.Cons (size, sizes) -> (
        let tbl = Bottom_up.grow_at_size cfg size tbl in
        report_progress on_progress size tbl;
        match find_first_in_ctrees ~cache ~var size tbl with
        | Some result -> Some result
        | None -> loop tbl sizes)
  in
  loop Component_set.empty diagonal_forever

let find_all_top_attacks ?on_progress ~var cfg bound =
  let sizes = Partition.diagonal_up_to bound in
  let cache = create_analysis_cache () in
  let rec loop tbl results = function
    | [] -> List.rev results
    | size :: sizes ->
        let tbl = Bottom_up.grow_at_size cfg size tbl in
        report_progress on_progress size tbl;
        let new_results = find_all_in_ctrees ~cache ~var size tbl in
        loop tbl (List.rev_append new_results results) sizes
  in
  loop Component_set.empty [] sizes
