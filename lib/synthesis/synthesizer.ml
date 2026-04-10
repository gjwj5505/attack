open Language

module Table = Component_table
module ExpSet = Component_table.ExpSet
module CmdSet = Component_table.CmdSet
module ETreeSet = Component_table.ETreeSet
module CTreeSet = Component_table.CTreeSet

type seeds = {
  ints : int list;
  vars : string list;
  envs : Environment.t list;
}

let empty_seeds = { ints = []; vars = []; envs = [] }

let dedup cmp xs = List.sort_uniq cmp xs

let normalize_seeds s =
  {
    ints = dedup Int.compare s.ints;
    vars = dedup String.compare s.vars;
    envs = dedup Stdlib.compare s.envs;
  }

let prog_size = Size_pair.prog_size
let proof_size = Size_pair.proof_size

let size_pairs_up_to bound = Size_pair.diagonal_up_to bound
let smaller_sizes target = Size_pair.all_smaller target

let ordered_partitions target parts =
  let pool = smaller_sizes target in
  let rec aux remaining_parts remaining =
    if remaining_parts = 0 then
      if Size_pair.equal remaining (Size_pair.make 0 0) then [ [] ] else []
    else
      pool
      |> List.filter (fun piece ->
             prog_size piece >= 1
             && proof_size piece >= 0
             && prog_size piece <= prog_size remaining
             && proof_size piece <= proof_size remaining)
      |> List.concat_map (fun piece ->
             let rest = Size_pair.sub remaining piece in
             if not (Size_pair.is_valid rest) then []
             else
               aux (remaining_parts - 1) rest
               |> List.map (fun suffix -> piece :: suffix))
  in
  aux parts target

let proof_partitions target parts root_cost =
  let residual = Size_pair.sub target root_cost in
  if not (Size_pair.is_valid residual) then []
  else ordered_partitions residual parts

let expr_partitions target parts root_prog_cost =
  let residual = Size_pair.sub target (Size_pair.make root_prog_cost 0) in
  if not (Size_pair.is_valid residual) || proof_size residual <> 0 then []
  else
    ordered_partitions residual parts
    |> List.filter (List.for_all Size_pair.is_raw_component)

let env_of_etree et =
  let env, _, _ = BigStep.get_e_concl et in
  env

let exp_of_etree et =
  let _, e, _ = BigStep.get_e_concl et in
  e

let value_of_etree et = BigStep.get_eval_val et

let env_of_ctree ct =
  let env, _, _ = BigStep.get_c_concl ct in
  env

let cmd_of_ctree ct =
  let _, c, _ = BigStep.get_c_concl ct in
  c

let final_env_of_ctree ct = BigStep.get_last_env ct

let eval_bop op v1 v2 =
  match op with
  | Syntax.Exp.Plus -> v1 + v2
  | Minus -> v1 - v2
  | Times -> v1 * v2
  | Eq -> if v1 = v2 then 1 else 0
  | Ne -> if v1 <> v2 then 1 else 0
  | Lt -> if v1 < v2 then 1 else 0
  | Le -> if v1 <= v2 then 1 else 0
  | Gt -> if v1 > v2 then 1 else 0
  | Ge -> if v1 >= v2 then 1 else 0

let bop_choices =
  [
    Syntax.Exp.Eq;
    Lt;
    Gt;
    Ne;
    Le;
    Ge;
    Plus;
    Minus;
    Times;
  ]

let fold_unary_partition f init parts =
  List.fold_left
    (fun acc part ->
      match part with
      | [ s1 ] -> f acc s1
      | _ -> acc)
    init parts

let fold_binary_partition f init parts =
  List.fold_left
    (fun acc part ->
      match part with
      | [ s1; s2 ] -> f acc s1 s2
      | _ -> acc)
    init parts

let fold_ternary_partition f init parts =
  List.fold_left
    (fun acc part ->
      match part with
      | [ s1; s2; s3 ] -> f acc s1 s2 s3
      | _ -> acc)
    init parts

let seed_raw_components seeds tbl =
  let tbl =
    List.fold_left
      (fun acc n -> Table.add_exp_exact (Syntax.Exp.Int n) acc)
      tbl seeds.ints
  in
  List.fold_left
    (fun acc x -> Table.add_exp_exact (Syntax.Exp.Var x) acc)
    tbl seeds.vars

let generate_raw_exps target tbl =
  if proof_size target <> 0 then tbl
  else
    let unary_sizes = expr_partitions target 1 1 in
    let binary_sizes = expr_partitions target 2 1 in
    let tbl =
      fold_unary_partition
        (fun acc s1 ->
          ExpSet.fold
            (fun e acc' ->
              Table.add_exp target (Syntax.Exp.Uop (Syntax.Exp.Uminus, e)) acc')
            (Table.exps_of_size s1 acc) acc)
        tbl unary_sizes
    in
    fold_binary_partition
      (fun acc s1 s2 ->
        ExpSet.fold
          (fun e1 acc1 ->
            ExpSet.fold
              (fun e2 acc2 ->
                List.fold_left
                  (fun acc3 op ->
                    Table.add_exp target (Syntax.Exp.Bop (op, e1, e2)) acc3)
                  acc2 bop_choices)
              (Table.exps_of_size s2 acc1) acc1)
          (Table.exps_of_size s1 acc) acc)
      tbl binary_sizes

let generate_raw_cmds target vars tbl =
  if proof_size target <> 0 then tbl
  else
    let assign_sizes = expr_partitions target 1 1 in
    let seq_sizes = expr_partitions target 2 1 in
    let if_sizes = expr_partitions target 3 1 in
    let while_sizes = expr_partitions target 2 1 in
    let tbl =
      fold_unary_partition
        (fun acc se ->
          List.fold_left
            (fun acc' x ->
              ExpSet.fold
                (fun e acc'' -> Table.add_cmd target (Syntax.Cmd.Assign (x, e)) acc'')
                (Table.exps_of_size se acc') acc')
            acc vars)
        tbl assign_sizes
    in
    let tbl =
      fold_binary_partition
        (fun acc s1 s2 ->
          CmdSet.fold
            (fun c1 acc1 ->
              CmdSet.fold
                (fun c2 acc2 ->
                  Table.add_cmd target
                    (Syntax.Cmd.Seq ({ Syntax.Cmd.lbl = 0; cmd = c1 }, { lbl = 0; cmd = c2 }))
                    acc2)
                (Table.cmds_of_size s2 acc1) acc1)
            (Table.cmds_of_size s1 acc) acc)
        tbl seq_sizes
    in
    let tbl =
      fold_ternary_partition
        (fun acc sp sc1 sc2 ->
          ExpSet.fold
            (fun pred acc1 ->
              CmdSet.fold
                (fun c1 acc2 ->
                  CmdSet.fold
                    (fun c2 acc3 ->
                      Table.add_cmd target
                        (Syntax.Cmd.If
                           ( pred,
                             { Syntax.Cmd.lbl = 0; cmd = c1 },
                             { lbl = 0; cmd = c2 } ))
                        acc3)
                    (Table.cmds_of_size sc2 acc2) acc2)
                (Table.cmds_of_size sc1 acc1) acc1)
            (Table.exps_of_size sp acc) acc)
        tbl if_sizes
    in
    fold_binary_partition
      (fun acc sp sc ->
        ExpSet.fold
          (fun pred acc1 ->
            CmdSet.fold
              (fun body acc2 ->
                Table.add_cmd target
                  (Syntax.Cmd.While (pred, { Syntax.Cmd.lbl = 0; cmd = body }))
                  acc2)
              (Table.cmds_of_size sc acc1) acc1)
          (Table.exps_of_size sp acc) acc)
      tbl while_sizes

let generate_etrees target seeds tbl =
  if proof_size target < 1 then tbl
  else
    let tbl =
      if Size_pair.equal target (Size_pair.make 1 1) then
        let tbl =
          List.fold_left
            (fun acc env ->
              List.fold_left
                (fun acc' n ->
                  Table.add_etree target
                    (BigStep.EInt ((), (env, Syntax.Exp.Int n, n)))
                    acc')
                acc seeds.ints)
            tbl seeds.envs
        in
        List.fold_left
          (fun acc env ->
            List.fold_left
              (fun acc' x ->
                let v = Environment.lookup x env in
                Table.add_etree target (BigStep.EVar ((), (env, Syntax.Exp.Var x, v))) acc')
              acc seeds.vars)
          tbl seeds.envs
      else tbl
    in
    let unary_parts = proof_partitions target 1 (Size_pair.make 1 1) in
    let binary_parts = proof_partitions target 2 (Size_pair.make 1 1) in
    let tbl =
      fold_unary_partition
        (fun acc s1 ->
          ETreeSet.fold
            (fun et acc' ->
              let env = env_of_etree et in
              let e = exp_of_etree et in
              let v = value_of_etree et in
              Table.add_etree target
                (BigStep.EUop
                   ( et,
                     (env, Syntax.Exp.Uop (Syntax.Exp.Uminus, e), -v) ))
                acc')
            (Table.etrees_of_size s1 acc) acc)
        tbl unary_parts
    in
    fold_binary_partition
      (fun acc s1 s2 ->
        ETreeSet.fold
          (fun et1 acc1 ->
            ETreeSet.fold
              (fun et2 acc2 ->
                let env1 = env_of_etree et1 in
                let env2 = env_of_etree et2 in
                if env1 <> env2 then acc2
                else
                  let e1 = exp_of_etree et1 in
                  let e2 = exp_of_etree et2 in
                  let v1 = value_of_etree et1 in
                  let v2 = value_of_etree et2 in
                  List.fold_left
                    (fun acc3 op ->
                      let v = eval_bop op v1 v2 in
                      Table.add_etree target
                        (BigStep.EBop
                           ( (et1, et2),
                             (env1, Syntax.Exp.Bop (op, e1, e2), v) ))
                        acc3)
                    acc2 bop_choices)
              (Table.etrees_of_size s2 acc1) acc1)
          (Table.etrees_of_size s1 acc) acc)
      tbl binary_parts

let generate_assign_ctrees target vars tbl =
  let residual = Size_pair.sub target (Size_pair.make 1 1) in
  if not (Size_pair.is_proof_component residual) then tbl
  else
    ETreeSet.fold
      (fun et acc ->
        let env = env_of_etree et in
        let e = exp_of_etree et in
        let v = value_of_etree et in
        List.fold_left
          (fun acc' x ->
            let env' = Environment.update x v env in
            Table.add_ctree target
              (BigStep.Assign (et, (env, Syntax.Cmd.Assign (x, e), env')))
              acc')
          acc vars)
      (Table.etrees_of_size residual tbl) tbl

let generate_seq_ctrees target tbl =
  let seq_parts = proof_partitions target 2 (Size_pair.make 1 1) in
  fold_binary_partition
    (fun acc s1 s2 ->
      CTreeSet.fold
        (fun ct1 acc1 ->
          CTreeSet.fold
            (fun ct2 acc2 ->
              let env = env_of_ctree ct1 in
              let env_mid = final_env_of_ctree ct1 in
              if env_mid <> env_of_ctree ct2 then acc2
              else
                Table.add_ctree target
                  (BigStep.Seq
                     ( (ct1, ct2),
                       ( env,
                         Syntax.Cmd.Seq
                           ( { Syntax.Cmd.lbl = 0; cmd = cmd_of_ctree ct1 },
                             { lbl = 0; cmd = cmd_of_ctree ct2 } ),
                         final_env_of_ctree ct2 ) ))
                  acc2)
            (Table.ctrees_of_size s2 acc1) acc1)
        (Table.ctrees_of_size s1 acc) acc)
    tbl seq_parts

let generate_if_ctrees target tbl =
  let root = Size_pair.make 1 1 in
  smaller_sizes target
  |> List.fold_left
       (fun acc sp ->
         smaller_sizes target
         |> List.fold_left
              (fun acc' sc ->
                let other_size =
                  Size_pair.sub (Size_pair.sub (Size_pair.sub target root) sp) sc
                in
                if not (Size_pair.is_proof_component sp)
                   || not (Size_pair.is_proof_component sc)
                   || not (Size_pair.is_raw_component other_size)
                then acc'
                else
                  ETreeSet.fold
                    (fun et acc1 ->
                      CTreeSet.fold
                        (fun ct acc2 ->
                          let env = env_of_etree et in
                          if env <> env_of_ctree ct then acc2
                          else
                            let pred = exp_of_etree et in
                            let branch = cmd_of_ctree ct in
                            let env' = final_env_of_ctree ct in
                            CmdSet.fold
                              (fun other acc3 ->
                                if value_of_etree et <> 0 then
                                  Table.add_ctree target
                                    (BigStep.IfTrue
                                       ( (et, ct),
                                         ( env,
                                           Syntax.Cmd.If
                                             ( pred,
                                               { Syntax.Cmd.lbl = 0; cmd = branch },
                                               { lbl = 0; cmd = other } ),
                                           env' ) ))
                                    acc3
                                else
                                  Table.add_ctree target
                                    (BigStep.IfFalse
                                       ( (et, ct),
                                         ( env,
                                           Syntax.Cmd.If
                                             ( pred,
                                               { Syntax.Cmd.lbl = 0; cmd = other },
                                               { lbl = 0; cmd = branch } ),
                                           env' ) ))
                                    acc3)
                              (Table.cmds_of_size other_size acc2) acc2)
                        (Table.ctrees_of_size sc acc1) acc1)
                    (Table.etrees_of_size sp acc') acc')
              acc)
       tbl

let generate_while_false_ctrees target tbl =
  let root = Size_pair.make 1 1 in
  smaller_sizes target
  |> List.fold_left
       (fun acc sp ->
         let body_size = Size_pair.sub (Size_pair.sub target root) sp in
         if not (Size_pair.is_proof_component sp)
            || not (Size_pair.is_raw_component body_size)
         then acc
         else
           ETreeSet.fold
             (fun et acc1 ->
               if value_of_etree et <> 0 then acc1
               else
                 let env = env_of_etree et in
                 let pred = exp_of_etree et in
                 CmdSet.fold
                   (fun body acc2 ->
                     Table.add_ctree target
                       (BigStep.WhileFalse
                          ( et,
                            ( env,
                              Syntax.Cmd.While
                                (pred, { Syntax.Cmd.lbl = 0; cmd = body }),
                              env ) ))
                       acc2)
                   (Table.cmds_of_size body_size acc1) acc1)
             (Table.etrees_of_size sp acc) acc)
       tbl

let generate_while_true_ctrees target tbl =
  let while_parts = proof_partitions target 3 (Size_pair.make 1 1) in
  fold_ternary_partition
    (fun acc sp sb sr ->
      ETreeSet.fold
        (fun et acc1 ->
          CTreeSet.fold
            (fun body acc2 ->
              CTreeSet.fold
                (fun rest acc3 ->
                  let env = env_of_etree et in
                  if value_of_etree et = 0
                     || env <> env_of_ctree body
                     || final_env_of_ctree body <> env_of_ctree rest
                  then acc3
                  else
                    Table.add_ctree target
                      (BigStep.WhileTrue
                         ( (et, body, rest),
                           ( env,
                             Syntax.Cmd.While
                               ( exp_of_etree et,
                                 { Syntax.Cmd.lbl = 0; cmd = cmd_of_ctree body } ),
                             final_env_of_ctree rest ) ))
                      acc3)
                (Table.ctrees_of_size sr acc2) acc2)
            (Table.ctrees_of_size sb acc1) acc1)
        (Table.etrees_of_size sp acc) acc)
    tbl while_parts

let generate_ctrees target vars tbl =
  if proof_size target < 1 then tbl
  else
    tbl
    |> generate_assign_ctrees target vars
    |> generate_seq_ctrees target
    |> generate_if_ctrees target
    |> generate_while_false_ctrees target
    |> generate_while_true_ctrees target

let step target seeds tbl =
  let tbl = generate_raw_exps target tbl in
  let tbl = generate_raw_cmds target seeds.vars tbl in
  let tbl = generate_etrees target seeds tbl in
  generate_ctrees target seeds.vars tbl

let enumerate_up_to seeds bound =
  let seeds = normalize_seeds seeds in
  let tbl = seed_raw_components seeds Table.empty in
  size_pairs_up_to bound
  |> List.fold_left
       (fun acc size ->
         if Size_pair.compare size (Size_pair.make 1 0) < 0 then acc
         else step size seeds acc)
       tbl
