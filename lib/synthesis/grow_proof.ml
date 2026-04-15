open Language

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

let grow_at_size cfg target tbl =
  tbl |> grow_eint cfg target |> grow_evar cfg target
