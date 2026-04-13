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

let fold_exps size tbl f acc =
  Component_set.ExpSet.fold f (Component_set.exps_of_size size tbl) acc

let grow_uop target tbl =
  let payload = Size.sub target (Size.make 1 0) in
  Partition.partition_with_constraints payload [ Partition.prog_component ]
  |> List.fold_left
       (fun tbl -> function
         | [ e_size ] ->
             fold_exps e_size tbl
               (fun e tbl ->
                 Component_set.add_exp target
                   (Syntax.Exp.Uop (Syntax.Exp.Uminus, e))
                   tbl)
               tbl
         | _ -> tbl)
       tbl

let grow_bop target tbl =
  let payload = Size.sub target (Size.make 1 0) in
  let bops =
    Syntax.Exp.[ Eq; Lt; Gt; Ne; Le; Ge; Plus; Minus; Times ]
  in
  Partition.partition_with_constraints payload
    [ Partition.prog_component; Partition.prog_component ]
  |> List.fold_left
       (fun tbl -> function
         | [ e1_size; e2_size ] ->
             fold_exps e1_size tbl
               (fun e1 tbl ->
                 fold_exps e2_size tbl
                   (fun e2 tbl ->
                     List.fold_left
                       (fun tbl op ->
                         Component_set.add_exp target
                           (Syntax.Exp.Bop (op, e1, e2))
                           tbl)
                       tbl bops)
                   tbl)
               tbl
         | _ -> tbl)
       tbl

let grow_prog_at_size target tbl =
  if Size.proof_size target <> 0 then tbl
  else tbl |> grow_uop target |> grow_bop target

let grow_at_size (_cfg : config) (target : Size.size) tbl =
  grow_prog_at_size target tbl

let build_up_to cfg bound =
  let sizes = Partition.diagonal_up_to bound in
  let tbl = add_initial_components cfg Component_set.empty in
  List.fold_left (fun tbl size -> grow_at_size cfg size tbl) tbl sizes
