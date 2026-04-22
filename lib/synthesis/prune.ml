open Language

let do_prune = true

let keep_exp exp =
  if not do_prune then true else
  match exp with
  | Syntax.Exp.Uop (Syntax.Exp.Uminus, Syntax.Exp.Int _) -> false
  | Syntax.Exp.Uop (Syntax.Exp.Uminus, Syntax.Exp.Uop (Syntax.Exp.Uminus, _)) ->
      false
  | _ -> true

let keep_cmd cmd =
  if not do_prune then true else
  match cmd with
  | Syntax.Cmd.Seq (_, { Syntax.Cmd.cmd = Seq _; _ }) -> false
  | _ -> true

let keep_etree etree =
  if not do_prune then true else
  let _, exp, _ = BigStep.get_e_concl etree in
  keep_exp exp

let keep_ctree ctree =
  if not do_prune then true else
  let _, cmd, _ = BigStep.get_c_concl ctree in
  keep_cmd cmd
