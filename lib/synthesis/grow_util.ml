let fold_exps size tbl f acc =
  Component_set.fold_exps size tbl f acc

let fold_cmds size tbl f acc =
  Component_set.fold_cmds size tbl f acc

let fold_etrees size tbl f acc =
  Component_set.fold_etrees size tbl f acc

let fold_ctrees size tbl f acc =
  Component_set.fold_ctrees size tbl f acc

let binary_fanout_cap = 32

let ternary_fanout_cap = 10

let take_n n xs =
  let rec loop k xs acc =
    match (k, xs) with
    | 0, _ -> List.rev acc
    | _, [] -> List.rev acc
    | k, x :: xs -> loop (k - 1) xs (x :: acc)
  in
  loop n xs []

let fold_some_exps cap size tbl f acc =
  Component_set.select_exps size tbl |> take_n cap |> List.fold_left (fun acc e -> f e acc) acc

let fold_some_cmds cap size tbl f acc =
  Component_set.select_cmds size tbl |> take_n cap |> List.fold_left (fun acc c -> f c acc) acc

let fold_some_etrees cap size tbl f acc =
  Component_set.select_etrees size tbl
  |> take_n cap
  |> List.fold_left (fun acc et -> f et acc) acc

let fold_some_ctrees cap size tbl f acc =
  Component_set.select_ctrees size tbl
  |> take_n cap
  |> List.fold_left (fun acc ct -> f ct acc) acc
