open BigStep
open Syntax

type result = Ok | Error of string

(* 유틸리티: 여러 결과를 순차적으로 확인 *)
let (>>=) res f = match res with Ok -> f () | Error _ as err -> err

(* 식(Expression) 검증 *)
let rec check_etree = function
| EInt ((), (_env, e, v)) ->
    (match e with
        | Exp.Int n -> if n = v then Ok else Error (Printf.sprintf "E-Int: %d != %d" n v)
        | _ -> Error "E-Int: Syntax mismatch")

| EVar ((), (env, e, v)) ->
    (match e with
        | Exp.Var x -> 
            if Environment.lookup x env = v then Ok
            else Error (Printf.sprintf "E-Var: Lookup %s failed" x)
        | _ -> Error "E-Var: Syntax mismatch")

| EBop ((t1, t2), (_env, e, v)) ->
    check_etree t1 >>= fun () ->
    check_etree t2 >>= fun () ->
    (match e with
        | Exp.Bop (op, _, _) ->
            let v1, v2 = get_eval_val t1, get_eval_val t2 in
            let expected = match op with
            | Plus -> v1 + v2 | Minus -> v1 - v2 | Times -> v1 * v2
            | Eq -> if v1 = v2 then 1 else 0 | Ne -> if v1 <> v2 then 1 else 0
            | Lt -> if v1 < v2 then 1 else 0 | Le -> if v1 <= v2 then 1 else 0
            | Gt -> if v1 > v2 then 1 else 0 | Ge -> if v1 >= v2 then 1 else 0
            in
            if v = expected then Ok else Error "E-Bop: Result mismatch"
        | _ -> Error "E-Bop: Syntax mismatch")

| EUop (t1, (_env, e, v)) ->
    check_etree t1 >>= fun () ->
    (match e with
        | Exp.Uop (op, _) ->
            let v1 = get_eval_val t1 in
            let expected = if op = Exp.Uminus then -v1 else v1 in
            if v = expected then Ok else Error "E-Uop: Result mismatch"
        | _ -> Error "E-Uop: Syntax mismatch")

(* 문장(Command) 검증 *)
let rec check_ctree = function
  | CAssign (et, (env, c, env')) ->
      check_etree et >>= fun () ->
      (match c with
          | Cmd.Assign (x, _) ->
              let v = get_eval_val et in
              if env' = Environment.update x v env then Ok
              else Error "S-Assign: Environment update mismatch"
          | _ -> Error "S-Assign: Syntax mismatch")

  | CSeq ((t1, t2), (_env, _c, env_final)) ->
      check_ctree t1 >>= fun () ->
      check_ctree t2 >>= fun () ->
      let env_mid = get_last_env t1 in
      let env_start2 = (match t2 with 
          | CAssign (_, (e, _, _)) | CSeq (_, (e, _, _))
          | CIfTrue (_, (e, _, _)) | CIfFalse (_, (e, _, _))
          | CWhileTrue (_, (e, _, _)) | CWhileFalse (_, (e, _, _)) -> e) in
      if env_mid = env_start2 && get_last_env t2 = env_final then Ok
      else Error "S-Seq: Environment flow broken"

  | CIfTrue ((et, ct), (_env, _c, env_final)) ->
      check_etree et >>= fun () ->
      check_ctree ct >>= fun () ->
      let v_If = get_eval_val et in
      if v_If = 0 then Error "S-IfTrue: If Condition should be non-zero"
      else
          let env_after_branch = get_last_env ct in
          if env_after_branch = env_final then Ok
          else Error "S-IfTrue: Final environment mismatch"

  | CIfFalse ((et, ct), (_env, _c, env_final)) ->
      check_etree et >>= fun () ->
      check_ctree ct >>= fun () ->
      let v_If = get_eval_val et in
      if v_If <> 0 then Error "S-IfFalse: If Condition should be zero"
      else
          let env_after_branch = get_last_env ct in
          if env_after_branch = env_final then Ok
          else Error "S-IfFalse: Final environment mismatch"

  | CWhileTrue ((et, t_body, t_rest), (_env, _c, env_final)) ->
      check_etree et >>= fun () ->
      check_ctree t_body >>= fun () ->
      check_ctree t_rest >>= fun () ->
      if get_eval_val et <> 0 && get_last_env t_rest = env_final then Ok
      else Error "S-WhileTrue: Logic or environment mismatch"

  | CWhileFalse (et, (env, _c, env_final)) ->
      check_etree et >>= fun () ->
      if get_eval_val et = 0 && env = env_final then Ok
      else Error "S-WhileFalse: Should not change state or If Condition not zero"
