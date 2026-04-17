open Language

type config = Config.t

let grow_at_size (cfg : config) (target : Size.size) tbl =
  tbl |> Grow_prog.grow_at_size cfg target |> Grow_proof.grow_at_size cfg target
  (* CWhileTrue는 같은 while command를 증명하는 rest ctree를 참조한다.
    rest는 target과 prog_size가 같지만 proof_size가 더 작으므로,
    diagonal order로 grow하면 항상 먼저 생성되어 있다. *)

let build_up_to cfg bound =
  let sizes = Partition.diagonal_up_to bound in
  List.fold_left
    (fun tbl size -> grow_at_size cfg size tbl)
    Component_set.empty sizes
