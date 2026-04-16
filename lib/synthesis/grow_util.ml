let fold_exps size tbl f acc =
  Component_set.ExpSet.fold f (Component_set.exps_of_size size tbl) acc

let fold_cmds size tbl f acc =
  Component_set.CmdSet.fold f (Component_set.cmds_of_size size tbl) acc

let fold_etrees size tbl f acc =
  Component_set.ETreeSet.fold f (Component_set.etrees_of_size size tbl) acc

let fold_ctrees size tbl f acc =
  Component_set.CTreeSet.fold f (Component_set.ctrees_of_size size tbl) acc
