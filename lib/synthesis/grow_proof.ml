open Language

let add_pruned_etree size etree tbl =
  if Prune.keep_etree etree then Component_set.add_etree size etree tbl else tbl

let add_pruned_ctree size ctree tbl =
  if Prune.keep_ctree ctree then Component_set.add_ctree size ctree tbl else tbl

let equal_cenv cenv1 cenv2 = Environment.VarMap.equal Int.equal cenv1 cenv2

let equal_whileloop_nolbl e c_inner c =
  Syntax.Cmd.equal_nolbl (Syntax.Cmd.While (e, Syntax.Cmd.dummy_lbl c_inner)) c

let calculate_uop op cval = Syntax.Exp.(match op with Uminus -> -cval)

let calculate_bop op cval1 cval2 =
  Syntax.Exp.(
    match op with
    | Eq -> if cval1 = cval2 then 1 else 0
    | Lt -> if cval1 < cval2 then 1 else 0
    | Gt -> if cval1 > cval2 then 1 else 0
    | Ne -> if cval1 <> cval2 then 1 else 0
    | Le -> if cval1 <= cval2 then 1 else 0
    | Ge -> if cval1 >= cval2 then 1 else 0
    | Plus -> cval1 + cval2
    | Minus -> cval1 - cval2
    | Times -> cval1 * cval2)

let is_eleaf_target target = Size.equal target (Size.make 1 1)

let grow_eint (cfg : Config.t) target tbl =
  if not (is_eleaf_target target) then tbl
  else
    Config_util.bounded_envs cfg
    |> List.fold_left
         (fun tbl cenv ->
           List.fold_left
             (fun tbl n ->
               add_pruned_etree target
                 (BigStep.EInt ((), (cenv, Syntax.Exp.Int n, n)))
                 tbl)
             tbl cfg.ints)
         tbl

let grow_evar (cfg : Config.t) target tbl =
  if not (is_eleaf_target target) then tbl
  else
    Config_util.bounded_envs cfg
    |> List.fold_left
         (fun tbl cenv ->
           List.fold_left
             (fun tbl x ->
               add_pruned_etree target
                 (BigStep.EVar
                    ((), (cenv, Syntax.Exp.Var x, Environment.lookup x cenv)))
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
                 let cenv, e, cval = BigStep.get_e_concl et in
                 List.fold_left
                   (fun tbl op ->
                     let cval = calculate_uop op cval in
                     add_pruned_etree target
                       (BigStep.EUop
                          (et, (cenv, Syntax.Exp.Uop (op, e), cval)))
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
             (* Original full fold:
                Grow_util.fold_etrees et1_size tbl *)
             Grow_util.fold_top_etrees Grow_util.binary_fanout_cap et1_size tbl
               (* TEMP: random-score fanout cap *)
               (fun et1 tbl ->
                 let cenv1, e1, cval1 = BigStep.get_e_concl et1 in
                 (* Original full fold:
                    Grow_util.fold_etrees et2_size tbl *)
                 Grow_util.fold_top_etrees Grow_util.binary_fanout_cap et2_size
                   tbl
                   (* TEMP: random-score fanout cap *)
                   (fun et2 tbl ->
                     let cenv2, e2, cval2 = BigStep.get_e_concl et2 in
                     if not (equal_cenv cenv1 cenv2) then tbl
                     else
                       List.fold_left
                         (fun tbl op ->
                           let cval = calculate_bop op cval1 cval2 in
                           add_pruned_etree target
                             (BigStep.EBop
                                ( (et1, et2),
                                  ( cenv1,
                                    Syntax.Exp.Bop (op, e1, e2),
                                    cval ) ))
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
                 let cenv, e, cval = BigStep.get_e_concl et in
                 if not (Config_util.is_in_bound cfg cval) then tbl
                 else
                   List.fold_left
                     (fun tbl x ->
                       let new_cenv = Environment.update x cval cenv in
                       add_pruned_ctree target
                         (BigStep.CAssign
                            (et, (cenv, Syntax.Cmd.Assign (x, e), new_cenv)))
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
             (* Original full fold:
                Grow_util.fold_ctrees ct1_size tbl *)
             Grow_util.fold_top_ctrees Grow_util.binary_fanout_cap ct1_size tbl
               (* TEMP: random-score fanout cap *)
               (fun ct1 tbl ->
                 let cenv1, c1, mid_cenv = BigStep.get_c_concl ct1 in
                 (* Original full fold:
                    Grow_util.fold_ctrees ct2_size tbl *)
                 Grow_util.fold_top_ctrees Grow_util.binary_fanout_cap ct2_size
                   tbl
                   (* TEMP: random-score fanout cap *)
                   (fun ct2 tbl ->
                     let cenv2, c2, final_cenv = BigStep.get_c_concl ct2 in
                     if not (equal_cenv mid_cenv cenv2) then tbl
                     else
                       add_pruned_ctree target
                         (BigStep.CSeq
                            ( (ct1, ct2),
                              ( cenv1,
                                Syntax.Cmd.Seq
                                  ( Syntax.Cmd.dummy_lbl c1,
                                    Syntax.Cmd.dummy_lbl c2 ),
                                final_cenv ) ))
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
             (* Original full fold:
                Grow_util.fold_etrees et_size tbl *)
             Grow_util.fold_top_etrees Grow_util.ternary_fanout_cap et_size tbl
               (* TEMP: random-score fanout cap *)
               (fun et tbl ->
                 let cenv1, e1, cval1 = BigStep.get_e_concl et in
                 if cval1 = 0 then tbl
                 else
                   (* Original full fold:
                      Grow_util.fold_ctrees ct_size tbl *)
                   Grow_util.fold_top_ctrees Grow_util.ternary_fanout_cap
                     ct_size tbl
                     (* TEMP: random-score fanout cap *)
                     (fun ct tbl ->
                       let cenv2, c2, branch_cenv = BigStep.get_c_concl ct in
                       if not (equal_cenv cenv1 cenv2) then tbl
                       else
                         (* Original full fold:
                            Grow_util.fold_cmds c_size tbl *)
                         Grow_util.fold_top_cmds Grow_util.ternary_fanout_cap
                           c_size tbl
                           (* TEMP: random-score fanout cap *)
                           (fun c3 tbl ->
                             add_pruned_ctree target
                               (BigStep.CIfTrue
                                  ( (et, ct),
                                    ( cenv1,
                                      Syntax.Cmd.If
                                        ( e1,
                                          Syntax.Cmd.dummy_lbl c2,
                                          Syntax.Cmd.dummy_lbl c3 ),
                                      branch_cenv ) ))
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
             (* Original full fold:
                Grow_util.fold_etrees et_size tbl *)
             Grow_util.fold_top_etrees Grow_util.ternary_fanout_cap et_size tbl
               (* TEMP: random-score fanout cap *)
               (fun et tbl ->
                 let cenv1, e1, cval1 = BigStep.get_e_concl et in
                 if cval1 <> 0 then tbl
                 else
                   (* Original full fold:
                      Grow_util.fold_ctrees ct_size tbl *)
                   Grow_util.fold_top_ctrees Grow_util.ternary_fanout_cap
                     ct_size tbl
                     (* TEMP: random-score fanout cap *)
                     (fun ct tbl ->
                       let cenv2, c2, branch_cenv = BigStep.get_c_concl ct in
                       if not (equal_cenv cenv1 cenv2) then tbl
                       else
                         (* Original full fold:
                            Grow_util.fold_cmds c_size tbl *)
                         Grow_util.fold_top_cmds Grow_util.ternary_fanout_cap
                           c_size tbl
                           (* TEMP: random-score fanout cap *)
                           (fun c3 tbl ->
                             add_pruned_ctree target
                               (BigStep.CIfFalse
                                  ( (et, ct),
                                    ( cenv1,
                                      Syntax.Cmd.If
                                        ( e1,
                                          Syntax.Cmd.dummy_lbl c3,
                                          Syntax.Cmd.dummy_lbl c2 ),
                                      branch_cenv ) ))
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
             (* Original full fold:
                Grow_util.fold_etrees et_size tbl *)
             Grow_util.fold_top_etrees Grow_util.ternary_fanout_cap et_size tbl
               (* TEMP: random-score fanout cap *)
               (fun et tbl ->
                 let cenv1, e1, cval1 = BigStep.get_e_concl et in
                 if cval1 = 0 then tbl
                 else
                   (* Original full fold:
                      Grow_util.fold_ctrees ct2_size tbl *)
                   Grow_util.fold_top_ctrees Grow_util.ternary_fanout_cap
                     ct2_size tbl
                     (* TEMP: random-score fanout cap *)
                     (fun ct2 tbl ->
                       let cenv2, c2, body_final_cenv =
                         BigStep.get_c_concl ct2
                       in
                       if not (equal_cenv cenv1 cenv2) then tbl
                       else
                         (* Original full fold:
                            Grow_util.fold_ctrees ct3_size tbl *)
                         Grow_util.fold_top_ctrees Grow_util.ternary_fanout_cap
                           ct3_size tbl
                           (* TEMP: random-score fanout cap *)
                           (fun ct3 tbl ->
                             let rest_init_cenv, c3, final_cenv =
                               BigStep.get_c_concl ct3
                             in
                             if not (equal_whileloop_nolbl e1 c2 c3) then tbl
                             else if
                               not (equal_cenv body_final_cenv rest_init_cenv)
                             then tbl
                             else
                               add_pruned_ctree target
                                 (BigStep.CWhileTrue
                                    ((et, ct2, ct3), (cenv1, c3, final_cenv)))
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
             (* Original full fold:
                Grow_util.fold_etrees et_size tbl *)
             Grow_util.fold_top_etrees Grow_util.binary_fanout_cap et_size tbl
               (* TEMP: random-score fanout cap *)
               (fun et tbl ->
                 let cenv, e, cval = BigStep.get_e_concl et in
                 if cval <> 0 then tbl
                 else
                   (* Original full fold:
                      Grow_util.fold_cmds c_size tbl *)
                   Grow_util.fold_top_cmds Grow_util.binary_fanout_cap c_size
                     tbl
                     (* TEMP: random-score fanout cap *)
                     (fun c tbl ->
                       add_pruned_ctree target
                         (BigStep.CWhileFalse
                            ( et,
                              ( cenv,
                                Syntax.Cmd.While (e, Syntax.Cmd.dummy_lbl c),
                                cenv ) ))
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
