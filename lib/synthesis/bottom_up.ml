open Language

type config = {
  vars : string list;
  ints : int list;
}

let add_initial_components (cfg : config) tbl =
  let tbl =
    List.fold_left
      (fun tbl n -> Component_set.add_exp_exact (Syntax.Exp.Int n) tbl)
      tbl cfg.ints
  in
  List.fold_left
    (fun tbl x -> Component_set.add_exp_exact (Syntax.Exp.Var x) tbl)
    tbl cfg.vars

let grow_at_size (_cfg : config) (target : Size.size) tbl =
  let _target = target in
  tbl

let build_up_to cfg bound =
  let sizes = Partition.diagonal_up_to bound in
  let tbl = add_initial_components cfg Component_set.empty in
  List.fold_left (fun tbl size -> grow_at_size cfg size tbl) tbl sizes
