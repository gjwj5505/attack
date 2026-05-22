(* Temporary fanout caps for the random-score experiment. These keep rule input
   products manageable until priority/diversity scheduling replaces them. *)
let binary_fanout_cap = 32

let ternary_fanout_cap = 10

let fold_exps = Component_set.fold_exps

let fold_cmds = Component_set.fold_cmds

let fold_etrees = Component_set.fold_etrees

let fold_ctrees = Component_set.fold_ctrees

let fold_top_exps = Component_set.fold_top_exps

let fold_top_cmds = Component_set.fold_top_cmds

let fold_top_etrees = Component_set.fold_top_etrees

let fold_top_ctrees = Component_set.fold_top_ctrees
