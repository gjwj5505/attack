open Language

type config = Config.t

let grow_at_size (cfg : config) (target : Size.size) tbl =
  tbl |> Grow_prog.grow_at_size cfg target |> Grow_proof.grow_at_size cfg target

let build_up_to cfg bound =
  let sizes = Partition.diagonal_up_to bound in
  List.fold_left
    (fun tbl size -> grow_at_size cfg size tbl)
    Component_set.empty sizes
