open BigStep
open Syntax

(* Expression Derivation *)
let rec derive_exp (e : Exp.t) (env : Environment.t) : etree =
  match e with
  | Exp.Int n -> 
      EInt ((), (env, e, n))

  | Exp.Var x -> 
      EVar ((), (env, e, Environment.lookup x env))

  | Exp.Uop (op, e1) ->
      let t1 = derive_exp e1 env in
      let v1 = get_eval_val t1 in
      let res = if op = Exp.Uminus then -v1 else v1 in
      EUop (t1, (env, e, res))

  | Exp.Bop (op, e1, e2) ->
      let t1 = derive_exp e1 env in
      let t2 = derive_exp e2 env in
      let v1, v2 = get_eval_val t1, get_eval_val t2 in
      let res = match op with
        | Plus  -> v1 + v2 | Minus -> v1 - v2 | Times -> v1 * v2
        | Eq -> if v1 = v2 then 1 else 0 | Ne -> if v1 <> v2 then 1 else 0
        | Lt -> if v1 < v2 then 1 else 0 | Le -> if v1 <= v2 then 1 else 0
        | Gt -> if v1 > v2 then 1 else 0 | Ge -> if v1 >= v2 then 1 else 0
      in
      EBop ((t1, t2), (env, e, res))

(* Command Derivation *)
let rec derive_cmd (lc : Cmd.lbl_t) (env : Environment.t) : ctree =
  let cmd_raw = lc.cmd in (* 원본 커맨드 *)
  match cmd_raw with
  | Cmd.Assign (x, e) ->
      let et = derive_exp e env in
      let v = get_eval_val et in
      let env' = Environment.update x v env in
      Assign (et, (env, cmd_raw, env'))

  | Cmd.Seq (c1, c2) ->
      let t1 = derive_cmd c1 env in
      let env_mid = get_last_env t1 in
      let t2 = derive_cmd c2 env_mid in
      let env_final = get_last_env t2 in
      Seq ((t1, t2), (env, cmd_raw, env_final))

  | Cmd.If (pred, con, alt) ->
      let pt = derive_exp pred env in
      if (get_eval_val pt) <> 0 then
        let t_con = derive_cmd con env in
        let env' = get_last_env t_con in
        IfTrue ((pt, t_con), (env, cmd_raw, env'))
      else
        let t_alt = derive_cmd alt env in
        let env' = get_last_env t_alt in
        IfFalse ((pt, t_alt), (env, cmd_raw, env'))

  | Cmd.While (pred, body) ->
      let pt = derive_exp pred env in
      if (get_eval_val pt) <> 0 then
        let t_body = derive_cmd body env in
        let env_next = get_last_env t_body in
        let t_rest = derive_cmd lc env_next in 
        let env_final = get_last_env t_rest in
        WhileTrue ((pt, t_body, t_rest), (env, cmd_raw, env_final))
      else
        WhileFalse (pt, (env, cmd_raw, env))