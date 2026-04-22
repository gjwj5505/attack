open Language

let do_prune = true

let is_commutative_bop =
  Syntax.Exp.(function Eq | Ne | Plus | Times -> true | _ -> false)

let rec exp_uses_var x = function
  | Syntax.Exp.Int _ -> false
  | Syntax.Exp.Var y -> x = y
  | Syntax.Exp.Uop (_, e) -> exp_uses_var x e
  | Syntax.Exp.Bop (_, e1, e2) -> exp_uses_var x e1 || exp_uses_var x e2

let independent_assigns x e1 y e2 =
  x <> y && not (exp_uses_var x e2) && not (exp_uses_var y e1)

let keep_exp exp =
  if not do_prune then true else
  match exp with
  | Syntax.Exp.Uop (Syntax.Exp.Uminus, Syntax.Exp.Int _) -> false (* -0 *)
  | Syntax.Exp.Uop (Syntax.Exp.Uminus, Syntax.Exp.Uop (Syntax.Exp.Uminus, _)) -> (* --x *)
      false
  | Syntax.Exp.Bop (op, e1, e2)
    when is_commutative_bop op && Stdlib.compare e1 e2 > 0 -> (* x + y = y + x *)
      false
  | Syntax.Exp.Bop (Syntax.Exp.Plus, Syntax.Exp.Int 0, _)
  | Syntax.Exp.Bop (Syntax.Exp.Plus, _, Syntax.Exp.Int 0) -> (* x + 0 = x *)
      false
  | Syntax.Exp.Bop (Syntax.Exp.Times, Syntax.Exp.Int 0, _)
  | Syntax.Exp.Bop (Syntax.Exp.Times, _, Syntax.Exp.Int 0) -> (* x * 0 = 0 *)
      false
  | Syntax.Exp.Bop (Syntax.Exp.Times, Syntax.Exp.Int 1, _)
  | Syntax.Exp.Bop (Syntax.Exp.Times, _, Syntax.Exp.Int 1) -> (* x * 1 = x *)
      false
  | _ -> true

let keep_cmd cmd =
  if not do_prune then true else
  match cmd with
  | Syntax.Cmd.Seq (_, { Syntax.Cmd.cmd = Seq _; _ }) -> false (* _; (_; _) = (_; _); _ *)
  | Syntax.Cmd.Seq
      ( { Syntax.Cmd.cmd = Assign (x, e1); _ },
        { Syntax.Cmd.cmd = Assign (y, e2); _ } )
    when independent_assigns x e1 y e2
         && Stdlib.compare (x, e1) (y, e2) > 0 ->
      false (* y := 1; x := 0 = x := 0; y := 1 *)
  | _ -> true



  

let keep_etree etree =
  if not do_prune then true else
  let _, exp, _ = BigStep.get_e_concl etree in
  keep_exp exp

let keep_ctree ctree =
  if not do_prune then true else
  let _, cmd, _ = BigStep.get_c_concl ctree in
  keep_cmd cmd
