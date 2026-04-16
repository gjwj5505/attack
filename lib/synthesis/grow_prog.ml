open Language

let fold_exps size tbl f acc =
  Component_set.ExpSet.fold f (Component_set.exps_of_size size tbl) acc

let fold_cmds size tbl f acc =
  Component_set.CmdSet.fold f (Component_set.cmds_of_size size tbl) acc

let is_eatom_target target = Size.equal target (Size.make 1 0)

let grow_int (cfg : Config.t) target tbl =
  if not (is_eatom_target target) then tbl
  else
    List.fold_left
      (fun tbl n -> Component_set.add_exp target (Syntax.Exp.Int n) tbl)
      tbl cfg.ints

let grow_var (cfg : Config.t) target tbl =
  if not (is_eatom_target target) then tbl
  else
    List.fold_left
      (fun tbl x -> Component_set.add_exp target (Syntax.Exp.Var x) tbl)
      tbl cfg.vars

let grow_uop (cfg : Config.t) target tbl =
  let payload = Size.sub target (Size.make 1 0) in
  Partition.partition_with_constraints payload [ Partition.prog_component ]
  |> List.fold_left
       (fun tbl -> function
         | [ e_size ] ->
             fold_exps e_size tbl
               (fun e tbl ->
                 List.fold_left
                   (fun tbl op ->
                     Component_set.add_exp target (Syntax.Exp.Uop (op, e)) tbl)
                   tbl cfg.uops)
               tbl
         | _ -> tbl)
       tbl

let grow_bop (cfg : Config.t) target tbl =
  let payload = Size.sub target (Size.make 1 0) in
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
                       tbl cfg.bops)
                   tbl)
               tbl
         | _ -> tbl)
       tbl

let grow_assign (cfg : Config.t) target tbl =
  let payload = Size.sub target (Size.make 1 0) in
  Partition.partition_with_constraints payload [ Partition.prog_component ]
  |> List.fold_left
       (fun tbl -> function
         | [ e_size ] ->
             fold_exps e_size tbl
               (fun e tbl ->
                 List.fold_left
                   (fun tbl x ->
                     Component_set.add_cmd target (Syntax.Cmd.Assign (x, e)) tbl)
                   tbl cfg.vars)
               tbl
         | _ -> tbl)
       tbl

let grow_seq target tbl =
  let payload = Size.sub target (Size.make 1 0) in
  Partition.partition_with_constraints payload
    [ Partition.prog_component; Partition.prog_component ]
  |> List.fold_left
       (fun tbl -> function
         | [ c1_size; c2_size ] ->
             fold_cmds c1_size tbl
               (fun c1 tbl ->
                 fold_cmds c2_size tbl
                   (fun c2 tbl ->
                     Component_set.add_cmd target
                       (Syntax.Cmd.Seq
                          (Syntax.Cmd.dummy_lbl c1, Syntax.Cmd.dummy_lbl c2))
                       tbl)
                   tbl)
               tbl
         | _ -> tbl)
       tbl

let grow_if target tbl =
  let payload = Size.sub target (Size.make 1 0) in
  Partition.partition_with_constraints payload
    [
      Partition.prog_component;
      Partition.prog_component;
      Partition.prog_component;
    ]
  |> List.fold_left
       (fun tbl -> function
         | [ e_size; c1_size; c2_size ] ->
             fold_exps e_size tbl
               (fun e tbl ->
                 fold_cmds c1_size tbl
                   (fun c1 tbl ->
                     fold_cmds c2_size tbl
                       (fun c2 tbl ->
                         Component_set.add_cmd target
                           (Syntax.Cmd.If
                              ( e,
                                Syntax.Cmd.dummy_lbl c1,
                                Syntax.Cmd.dummy_lbl c2 ))
                           tbl)
                       tbl)
                   tbl)
               tbl
         | _ -> tbl)
       tbl

let grow_while target tbl =
  let payload = Size.sub target (Size.make 1 0) in
  Partition.partition_with_constraints payload
    [ Partition.prog_component; Partition.prog_component ]
  |> List.fold_left
       (fun tbl -> function
         | [ e_size; c_size ] ->
             fold_exps e_size tbl
               (fun e tbl ->
                 fold_cmds c_size tbl
                   (fun c tbl ->
                     Component_set.add_cmd target
                       (Syntax.Cmd.While (e, Syntax.Cmd.dummy_lbl c))
                       tbl)
                   tbl)
               tbl
         | _ -> tbl)
       tbl

let grow_at_size cfg target tbl =
  if Size.proof_size target <> 0 then tbl
  else
    tbl |> grow_int cfg target |> grow_var cfg target |> grow_uop cfg target
    |> grow_bop cfg target |> grow_assign cfg target |> grow_seq target
    |> grow_if target |> grow_while target
