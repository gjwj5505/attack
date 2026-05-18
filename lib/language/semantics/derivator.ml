open BigStep
open Syntax

(* Expression Derivation *)
let rec derive_exp (e : Exp.t) (cenv : Environment.t) : etree =
  match e with
  | Exp.Int n -> EInt ((), (cenv, e, n))
  | Exp.Var x -> EVar ((), (cenv, e, Environment.lookup x cenv))
  | Exp.Uop (op, e1) ->
      let t1 = derive_exp e1 cenv in
      let cval1 = get_eval_val t1 in
      let cval = if op = Exp.Uminus then -cval1 else cval1 in
      EUop (t1, (cenv, e, cval))
  | Exp.Bop (op, e1, e2) ->
      let t1 = derive_exp e1 cenv in
      let t2 = derive_exp e2 cenv in
      let cval1, cval2 = (get_eval_val t1, get_eval_val t2) in
      let cval =
        match op with
        | Plus -> cval1 + cval2
        | Minus -> cval1 - cval2
        | Times -> cval1 * cval2
        | Eq -> if cval1 = cval2 then 1 else 0
        | Ne -> if cval1 <> cval2 then 1 else 0
        | Lt -> if cval1 < cval2 then 1 else 0
        | Le -> if cval1 <= cval2 then 1 else 0
        | Gt -> if cval1 > cval2 then 1 else 0
        | Ge -> if cval1 >= cval2 then 1 else 0
      in
      EBop ((t1, t2), (cenv, e, cval))

(* Command Derivation *)
let rec derive_cmd (lc : Cmd.lbl_t) (cenv : Environment.t) : ctree =
  let cmd_raw = lc.cmd in
  (* 원본 커맨드 *)
  match cmd_raw with
  | Cmd.Assign (x, e) ->
      let et = derive_exp e cenv in
      let cval = get_eval_val et in
      let next_cenv = Environment.update x cval cenv in
      CAssign (et, (cenv, cmd_raw, next_cenv))
  | Cmd.Seq (c1, c2) ->
      let t1 = derive_cmd c1 cenv in
      let mid_cenv = get_last_cenv t1 in
      let t2 = derive_cmd c2 mid_cenv in
      let final_cenv = get_last_cenv t2 in
      CSeq ((t1, t2), (cenv, cmd_raw, final_cenv))
  | Cmd.If (pred, con, alt) ->
      let pt = derive_exp pred cenv in
      if get_eval_val pt <> 0 then
        let t_con = derive_cmd con cenv in
        let branch_cenv = get_last_cenv t_con in
        CIfTrue ((pt, t_con), (cenv, cmd_raw, branch_cenv))
      else
        let t_alt = derive_cmd alt cenv in
        let branch_cenv = get_last_cenv t_alt in
        CIfFalse ((pt, t_alt), (cenv, cmd_raw, branch_cenv))
  | Cmd.While (pred, body) ->
      let pt = derive_exp pred cenv in
      if get_eval_val pt <> 0 then
        let t_body = derive_cmd body cenv in
        let next_cenv = get_last_cenv t_body in
        let t_rest = derive_cmd lc next_cenv in
        let final_cenv = get_last_cenv t_rest in
        CWhileTrue ((pt, t_body, t_rest), (cenv, cmd_raw, final_cenv))
      else CWhileFalse (pt, (cenv, cmd_raw, cenv))
