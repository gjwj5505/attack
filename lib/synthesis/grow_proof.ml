open Language

let fold_etrees size tbl f acc =
  Component_set.ETreeSet.fold f (Component_set.etrees_of_size size tbl) acc

let fold_ctrees size tbl f acc =
  Component_set.CTreeSet.fold f (Component_set.ctrees_of_size size tbl) acc

let equal_env e1 e2 =
  Environment.VarMap.equal Int.equal e1 e2

let calculate_uop op v =
  Syntax.Exp.(
    match op with
    | Uminus -> -v )

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

let is_eleaf_target target =
  Size.equal target (Size.make 1 1)

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
             fold_etrees et_size tbl
               (fun et tbl ->
                  let env, e, v = BigStep.get_e_concl et in
                  List.fold_left
                    (fun tbl op ->
                      let v = calculate_uop op v in
                      Component_set.add_etree target
                        (BigStep.EUop
                            ( et,
                              (env, Syntax.Exp.Uop (op, e), v) ))
                        tbl)
                    tbl cfg.uops)
               tbl
         | _ -> tbl)
       tbl

let grow_ebop (cfg : Config.t) target tbl = 
  let payload = Size.sub target (Size.make 1 1) in
  Partition.partition_with_constraints payload [ Partition.proof_component; Partition.proof_component ]
  |> List.fold_left
       (fun tbl -> function
         | [ et1_size; et2_size ] ->
             fold_etrees et1_size tbl
               (fun et1 tbl ->
                  let env1, e1, v1 = BigStep.get_e_concl et1 in
                  fold_etrees et2_size tbl
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
             fold_etrees et_size tbl
               (fun et tbl ->
                  let env, e, v = BigStep.get_e_concl et in
                  if not (Config.is_in_bound cfg v) then tbl
                  else
                  List.fold_left
                    (fun tbl x ->
                      let new_env = Environment.update x v env in
                      Component_set.add_ctree target
                        (BigStep.CAssign
                            ( et,
                              (env, Syntax.Cmd.Assign (x, e), new_env) ))
                        tbl)
                    tbl cfg.vars)
               tbl
         | _ -> tbl)
       tbl

       
let grow_cseq target tbl = 
  let payload = Size.sub target (Size.make 1 1) in
  Partition.partition_with_constraints payload [ Partition.proof_component; Partition.proof_component ]
  |> List.fold_left
       (fun tbl -> function
         | [ ct1_size; ct2_size ] ->
             fold_ctrees ct1_size tbl
               (fun ct1 tbl ->
                  let env1, c1, env1' = BigStep.get_c_concl ct1 in
                  fold_ctrees ct2_size tbl
                    (fun ct2 tbl ->
                      let env2, c2, env2' = BigStep.get_c_concl ct2 in
                      if not (equal_env env1' env2) then tbl
                      else
                      Component_set.add_ctree target
                        (BigStep.CSeq
                          ( (ct1, ct2),
                            ( env1,
                              Syntax.Cmd.Seq
                                (Syntax.Cmd.dummy_lbl c1, Syntax.Cmd.dummy_lbl c2),
                              env2' ) ))
                        tbl)
                   tbl)
               tbl
         | _ -> tbl)
       tbl


let grow_at_size cfg target tbl =
  tbl |> grow_eint cfg target |> grow_evar cfg target
  |> grow_euop cfg target |> grow_ebop cfg target
  |> grow_cassign cfg target
  |> grow_cseq target
