open BigStep
open Syntax

type result = Ok | Error of string

(* 유틸리티: 여러 결과를 순차적으로 확인 *)
let ( >>= ) res f = match res with Ok -> f () | Error _ as err -> err

(* 식(Expression) 검증 *)
let rec check_etree = function
  | EInt ((), (_cenv, e, cval)) -> (
      match e with
      | Exp.Int n ->
          if n = cval then Ok
          else Error (Printf.sprintf "E-Int: %d != %d" n cval)
      | _ -> Error "E-Int: Syntax mismatch")
  | EVar ((), (cenv, e, cval)) -> (
      match e with
      | Exp.Var x ->
          if Environment.lookup x cenv = cval then Ok
          else Error (Printf.sprintf "E-Var: Lookup %s failed" x)
      | _ -> Error "E-Var: Syntax mismatch")
  | EBop ((t1, t2), (_cenv, e, cval)) -> (
      check_etree t1 >>= fun () ->
      check_etree t2 >>= fun () ->
      match e with
      | Exp.Bop (op, _, _) ->
          let cval1, cval2 = (get_eval_val t1, get_eval_val t2) in
          let expected =
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
          if cval = expected then Ok else Error "E-Bop: Result mismatch"
      | _ -> Error "E-Bop: Syntax mismatch")
  | EUop (t1, (_cenv, e, cval)) -> (
      check_etree t1 >>= fun () ->
      match e with
      | Exp.Uop (op, _) ->
          let cval1 = get_eval_val t1 in
          let expected = if op = Exp.Uminus then -cval1 else cval1 in
          if cval = expected then Ok else Error "E-Uop: Result mismatch"
      | _ -> Error "E-Uop: Syntax mismatch")

(* 문장(Command) 검증 *)
let rec check_ctree = function
  | CAssign (et, (cenv, c, next_cenv)) -> (
      check_etree et >>= fun () ->
      match c with
      | Cmd.Assign (x, _) ->
          let cval = get_eval_val et in
          if next_cenv = Environment.update x cval cenv then Ok
          else Error "S-Assign: Environment update mismatch"
      | _ -> Error "S-Assign: Syntax mismatch")
  | CSeq ((t1, t2), (_cenv, _c, final_cenv)) ->
      check_ctree t1 >>= fun () ->
      check_ctree t2 >>= fun () ->
      let mid_cenv = get_last_cenv t1 in
      let start2_cenv =
        match t2 with
        | CAssign (_, (e, _, _))
        | CSeq (_, (e, _, _))
        | CIfTrue (_, (e, _, _))
        | CIfFalse (_, (e, _, _))
        | CWhileTrue (_, (e, _, _))
        | CWhileFalse (_, (e, _, _)) ->
            e
      in
      if mid_cenv = start2_cenv && get_last_cenv t2 = final_cenv then Ok
      else Error "S-Seq: Environment flow broken"
  | CIfTrue ((et, ct), (_cenv, _c, final_cenv)) ->
      check_etree et >>= fun () ->
      check_ctree ct >>= fun () ->
      let v_If = get_eval_val et in
      if v_If = 0 then Error "S-IfTrue: If Condition should be non-zero"
      else
        let branch_cenv = get_last_cenv ct in
        if branch_cenv = final_cenv then Ok
        else Error "S-IfTrue: Final environment mismatch"
  | CIfFalse ((et, ct), (_cenv, _c, final_cenv)) ->
      check_etree et >>= fun () ->
      check_ctree ct >>= fun () ->
      let v_If = get_eval_val et in
      if v_If <> 0 then Error "S-IfFalse: If Condition should be zero"
      else
        let branch_cenv = get_last_cenv ct in
        if branch_cenv = final_cenv then Ok
        else Error "S-IfFalse: Final environment mismatch"
  | CWhileTrue ((et, t_body, t_rest), (_cenv, _c, final_cenv)) ->
      check_etree et >>= fun () ->
      check_ctree t_body >>= fun () ->
      check_ctree t_rest >>= fun () ->
      if get_eval_val et <> 0 && get_last_cenv t_rest = final_cenv then Ok
      else Error "S-WhileTrue: Logic or environment mismatch"
  | CWhileFalse (et, (cenv, _c, final_cenv)) ->
      check_etree et >>= fun () ->
      if get_eval_val et = 0 && cenv = final_cenv then Ok
      else
        Error "S-WhileFalse: Should not change state or If Condition not zero"
