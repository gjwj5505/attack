let fold_exps size tbl f acc =
  Component_set.fold_exps size tbl f acc

let fold_cmds size tbl f acc =
  Component_set.fold_cmds size tbl f acc

let fold_etrees size tbl f acc =
  Component_set.fold_etrees size tbl f acc

let fold_ctrees size tbl f acc =
  Component_set.fold_ctrees size tbl f acc

let fold_some_exps rule size tbl f acc =
  Component_set.scored_exp_elements size tbl
  |> Heuristic.choose_current_for_grow rule |> List.map fst
  |> List.fold_left (fun acc e -> f e acc) acc

let fold_some_cmds rule size tbl f acc =
  Component_set.scored_cmd_elements size tbl
  |> Heuristic.choose_current_for_grow rule |> List.map fst
  |> List.fold_left (fun acc c -> f c acc) acc

let fold_some_etrees rule size tbl f acc =
  Component_set.scored_etree_elements size tbl
  |> Heuristic.choose_current_for_grow rule |> List.map fst
  |> List.fold_left (fun acc et -> f et acc) acc

let fold_some_ctrees rule size tbl f acc =
  Component_set.scored_ctree_elements size tbl
  |> Heuristic.choose_current_for_grow rule |> List.map fst
  |> List.fold_left (fun acc ct -> f ct acc) acc
