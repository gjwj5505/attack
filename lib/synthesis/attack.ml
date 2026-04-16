open Language

type result = {
  size : Size.size;
  tree : BigStep.ctree;
  cmd : Syntax.Cmd.t;
  analysis_result : Analyzer.Abs_mem.t;
}

let analysis_result_is_top var mem =
  Analyzer.Abs_val.is_top (Analyzer.Abs_mem.find var mem)

let analyze_cmd cmd =
  Analyzer.analysis (Syntax.Cmd.dummy_lbl cmd)

let check_ctree ~var size ct =
  let _, cmd, _ = BigStep.get_c_concl ct in
  let analysis_result = analyze_cmd cmd in
  if analysis_result_is_top var analysis_result then
    Some { size; tree = ct; cmd; analysis_result }
  else None

let find_in_ctrees ~var size tbl =
  Component_set.CTreeSet.to_seq (Component_set.ctrees_of_size size tbl)
  |> Seq.filter_map (check_ctree ~var size)
  |> Seq.uncons
  |> Option.map fst

let find_top_attack ~var cfg bound =
  let sizes = Partition.diagonal_up_to bound in
  let rec loop tbl = function
    | [] -> None
    | size :: sizes -> (
        let tbl = Bottom_up.grow_at_size cfg size tbl in
        match find_in_ctrees ~var size tbl with
        | Some result -> Some result
        | None -> loop tbl sizes)
  in
  loop Component_set.empty sizes
