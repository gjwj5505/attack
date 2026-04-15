open Language

let fold_etrees size tbl f acc =
  Component_set.ETreeSet.fold f (Component_set.etrees_of_size size tbl) acc

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

let grow_eint cfg target tbl =
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
             tbl cfg.Config.ints)
         tbl

let grow_evar cfg target tbl =
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
             tbl cfg.Config.vars)
         tbl
         
let grow_euop cfg target tbl = 
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
                    tbl cfg.Config.uops)
               tbl
         | _ -> tbl)
       tbl

let grow_ebop cfg target tbl = 
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
                         tbl cfg.Config.bops)
                   tbl)
               tbl
         | _ -> tbl)
       tbl

let grow_at_size cfg target tbl =
  tbl |> grow_eint cfg target |> grow_evar cfg target
  |> grow_euop cfg target |> grow_ebop cfg target
