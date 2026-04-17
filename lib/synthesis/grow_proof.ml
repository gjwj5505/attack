open Language

let equal_env e1 e2 = Environment.VarMap.equal Int.equal e1 e2

let equal_whileloop_nolbl e c_inner c =
  Syntax.Cmd.equal_nolbl (Syntax.Cmd.While (e, Syntax.Cmd.dummy_lbl c_inner)) c

let calculate_uop op v = Syntax.Exp.(match op with Uminus -> -v)

let calculate_bop op v1 v2 =
  Syntax.Exp.(
    match op with
    | Eq -> if v1 = v2 then 1 else 0
    | Lt -> if v1 < v2 then 1 else 0
    | Gt -> if v1 > v2 then 1 else 0
    | Ne -> if v1 <> v2 then 1 else 0
    | Le -> if v1 <= v2 then 1 else 0
    | Ge -> if v1 >= v2 then 1 else 0
    | Plus -> v1 + v2
    | Minus -> v1 - v2
    | Times -> v1 * v2)

let is_eleaf_target target = Size.equal target (Size.make 1 1)

let grow_eint (cfg : Config.t) target tbl =
  if not (is_eleaf_target target) then tbl
  else
    Config.bounded_envs cfg
    |> List.fold_left
         (fun tbl env ->
           List.fold_left
             (fun tbl n ->
               Component_set.add_etree target
                 (BigStep.EInt ((), (env, Syntax.Exp.Int n, n)))
                 tbl)
             tbl cfg.ints)
         tbl

let grow_evar (cfg : Config.t) target tbl =
  if not (is_eleaf_target target) then tbl
  else
    Config.bounded_envs cfg
    |> List.fold_left
         (fun tbl env ->
           List.fold_left
             (fun tbl x ->
               Component_set.add_etree target
                 (BigStep.EVar
                    ((), (env, Syntax.Exp.Var x, Environment.lookup x env)))
                 tbl)
             tbl cfg.vars)
         tbl

let grow_euop (cfg : Config.t) target tbl =
  let payload = Size.sub target (Size.make 1 1) in
  Partition.partition_with_constraints payload [ Partition.proof_component ]
  |> List.fold_left
       (fun tbl -> function
         | [ et_size ] ->
             Grow_util.fold_etrees et_size tbl
               (fun et tbl ->
                 let env, e, v = BigStep.get_e_concl et in
                 List.fold_left
                   (fun tbl op ->
                     let v = calculate_uop op v in
                     Component_set.add_etree target
                       (BigStep.EUop (et, (env, Syntax.Exp.Uop (op, e), v)))
                       tbl)
                   tbl cfg.uops)
               tbl
         | _ -> tbl)
       tbl

let grow_ebop (cfg : Config.t) target tbl =
  let payload = Size.sub target (Size.make 1 1) in
  Partition.partition_with_constraints payload
    [ Partition.proof_component; Partition.proof_component ]
  |> List.fold_left
       (fun tbl -> function
         | [ et1_size; et2_size ] ->
             Grow_util.fold_etrees et1_size tbl
               (fun et1 tbl ->
                 let env1, e1, v1 = BigStep.get_e_concl et1 in
                 Grow_util.fold_etrees et2_size tbl
                   (fun et2 tbl ->
                     let env2, e2, v2 = BigStep.get_e_concl et2 in
                     if not (equal_env env1 env2) then tbl
                     else
                       List.fold_left
                         (fun tbl op ->
                           let v = calculate_bop op v1 v2 in
                           Component_set.add_etree target
                             (BigStep.EBop
                                ( (et1, et2),
                                  (env1, Syntax.Exp.Bop (op, e1, e2), v) ))
                             tbl)
                         tbl cfg.bops)
                   tbl)
               tbl
         | _ -> tbl)
       tbl

let grow_cassign (cfg : Config.t) target tbl =
  let payload = Size.sub target (Size.make 1 1) in
  Partition.partition_with_constraints payload [ Partition.proof_component ]
  |> List.fold_left
       (fun tbl -> function
         | [ et_size ] ->
             Grow_util.fold_etrees et_size tbl
               (fun et tbl ->
                 let env, e, v = BigStep.get_e_concl et in
                 if not (Config.is_in_bound cfg v) then tbl
                 else
                   List.fold_left
                     (fun tbl x ->
                       let new_env = Environment.update x v env in
                       Component_set.add_ctree target
                         (BigStep.CAssign
                            (et, (env, Syntax.Cmd.Assign (x, e), new_env)))
                         tbl)
                     tbl cfg.vars)
               tbl
         | _ -> tbl)
       tbl

let grow_cseq target tbl =
  let payload = Size.sub target (Size.make 1 1) in
  Partition.partition_with_constraints payload
    [ Partition.proof_component; Partition.proof_component ]
  |> List.fold_left
       (fun tbl -> function
         | [ ct1_size; ct2_size ] ->
             Grow_util.fold_ctrees ct1_size tbl
               (fun ct1 tbl ->
                 let env1, c1, env1' = BigStep.get_c_concl ct1 in
                 Grow_util.fold_ctrees ct2_size tbl
                   (fun ct2 tbl ->
                     let env2, c2, env2' = BigStep.get_c_concl ct2 in
                     if not (equal_env env1' env2) then tbl
                     else
                       Component_set.add_ctree target
                         (BigStep.CSeq
                            ( (ct1, ct2),
                              ( env1,
                                Syntax.Cmd.Seq
                                  ( Syntax.Cmd.dummy_lbl c1,
                                    Syntax.Cmd.dummy_lbl c2 ),
                                env2' ) ))
                         tbl)
                   tbl)
               tbl
         | _ -> tbl)
       tbl

let grow_ciftrue target tbl =
  let payload = Size.sub target (Size.make 1 1) in
  Partition.partition_with_constraints payload
    [
      Partition.proof_component;
      Partition.proof_component;
      Partition.prog_component;
    ]
  |> List.fold_left
       (fun tbl -> function
         | [ et_size; ct_size; c_size ] ->
             Grow_util.fold_etrees et_size tbl
               (fun et tbl ->
                 let env1, e1, v1 = BigStep.get_e_concl et in
                 if v1 = 0 then tbl
                 else
                   Grow_util.fold_ctrees ct_size tbl
                     (fun ct tbl ->
                       let env2, c2, env2' = BigStep.get_c_concl ct in
                       if not (equal_env env1 env2) then tbl
                       else
                         Grow_util.fold_cmds c_size tbl
                           (fun c3 tbl ->
                             Component_set.add_ctree target
                               (BigStep.CIfTrue
                                  ( (et, ct),
                                    ( env1,
                                      Syntax.Cmd.If
                                        ( e1,
                                          Syntax.Cmd.dummy_lbl c2,
                                          Syntax.Cmd.dummy_lbl c3 ),
                                      env2' ) ))
                               tbl)
                           tbl)
                     tbl)
               tbl
         | _ -> tbl)
       tbl

let grow_ciffalse target tbl =
  let payload = Size.sub target (Size.make 1 1) in
  Partition.partition_with_constraints payload
    [
      Partition.proof_component;
      Partition.proof_component;
      Partition.prog_component;
    ]
  |> List.fold_left
       (fun tbl -> function
         | [ et_size; ct_size; c_size ] ->
             Grow_util.fold_etrees et_size tbl
               (fun et tbl ->
                 let env1, e1, v1 = BigStep.get_e_concl et in
                 if v1 <> 0 then tbl
                 else
                   Grow_util.fold_ctrees ct_size tbl
                     (fun ct tbl ->
                       let env2, c2, env2' = BigStep.get_c_concl ct in
                       if not (equal_env env1 env2) then tbl
                       else
                         Grow_util.fold_cmds c_size tbl
                           (fun c3 tbl ->
                             Component_set.add_ctree target
                               (BigStep.CIfFalse
                                  ( (et, ct),
                                    ( env1,
                                      Syntax.Cmd.If
                                        ( e1,
                                          Syntax.Cmd.dummy_lbl c3,
                                          Syntax.Cmd.dummy_lbl c2 ),
                                      env2' ) ))
                               tbl)
                           tbl)
                     tbl)
               tbl
         | _ -> tbl)
       tbl

let grow_cwhiletrue target tbl =
  Partition.partition_special_while target
  |> List.fold_left
       (fun tbl -> function
         | [ et_size; ct2_size; ct3_size ] ->
             Grow_util.fold_etrees et_size tbl
               (fun et tbl ->
                 let env1, e1, v1 = BigStep.get_e_concl et in
                 if v1 = 0 then tbl
                 else
                   Grow_util.fold_ctrees ct2_size tbl
                     (fun ct2 tbl ->
                       let env2, c2, env2' = BigStep.get_c_concl ct2 in
                       if not (equal_env env1 env2) then tbl
                       else
                         Grow_util.fold_ctrees ct3_size tbl
                           (fun ct3 tbl ->
                             let env3, c3, env3' = BigStep.get_c_concl ct3 in
                             if not (equal_whileloop_nolbl e1 c2 c3) then tbl
                             else if not (equal_env env2' env3) then tbl
                             else
                               Component_set.add_ctree target
                                 (BigStep.CWhileTrue
                                    ((et, ct2, ct3), (env1, c3, env3')))
                                 tbl)
                           tbl)
                     tbl)
               tbl
         | _ -> tbl)
       tbl

let grow_cwhilefalse target tbl =
  let payload = Size.sub target (Size.make 1 1) in
  Partition.partition_with_constraints payload
    [ Partition.proof_component; Partition.prog_component ]
  |> List.fold_left
       (fun tbl -> function
         | [ et_size; c_size ] ->
             Grow_util.fold_etrees et_size tbl
               (fun et tbl ->
                 let env, e, v = BigStep.get_e_concl et in
                 if v <> 0 then tbl
                 else
                   Grow_util.fold_cmds c_size tbl
                     (fun c tbl ->
                       Component_set.add_ctree target
                         (BigStep.CWhileFalse
                            ( et,
                              ( env,
                                Syntax.Cmd.While (e, Syntax.Cmd.dummy_lbl c),
                                env ) ))
                         tbl)
                     tbl)
               tbl
         | _ -> tbl)
       tbl

let grow_at_size cfg target tbl =
  tbl |> grow_eint cfg target |> grow_evar cfg target |> grow_euop cfg target
  |> grow_ebop cfg target |> grow_cassign cfg target |> grow_cseq target
  |> grow_ciftrue target |> grow_ciffalse target |> grow_cwhiletrue target
  |> grow_cwhilefalse target
