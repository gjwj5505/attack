let binary_fanout_cap = 10

let ternary_fanout_cap = 32

let fold_some cap xs f acc =
  let rec loop n xs acc =
    if n <= 0 then acc
    else
      match xs with
      | [] -> acc
      | x :: xs -> loop (n - 1) xs (f x acc)
  in
  loop cap xs acc

let fold_exps size tbl f acc =
  Component_set.fold_exps size tbl f acc

let fold_cmds size tbl f acc =
  Component_set.fold_cmds size tbl f acc

let fold_etrees size tbl f acc =
  Component_set.fold_etrees size tbl f acc

let fold_ctrees size tbl f acc =
  Component_set.fold_ctrees size tbl f acc

let fold_some_exps _cap size tbl f acc =
  fold_some _cap (Component_set.select_exps size tbl) f acc

let fold_some_cmds _cap size tbl f acc =
  fold_some _cap (Component_set.select_cmds size tbl) f acc

let fold_some_etrees _cap size tbl f acc =
  fold_some _cap (Component_set.select_etrees size tbl) f acc

let fold_some_ctrees _cap size tbl f acc =
  fold_some _cap (Component_set.select_ctrees size tbl) f acc
