open BigStep
open BigStepUtil

type result =
  | Valid
  | Invalid of string

let ok = Valid
let error msg = Invalid msg

let ( >>= ) res f =
  match res with
  | Valid -> f ()
  | Invalid _ as err -> err

let check_memory label expected actual =
  if expected = actual then ok else error (label ^ ": memory mismatch")

let check_value label expected actual =
  if expected = actual then ok else error (label ^ ": value mismatch")

let check_location label expected actual =
  if expected = actual then ok else error (label ^ ": location mismatch")

let check_control label expected actual =
  if expected = actual then ok else error (label ^ ": control mismatch")

let check_exp label expected actual =
  if SyntaxEqual.Exp.equal_t expected actual then ok
  else error (label ^ ": expression mismatch")

let check_lval label expected actual =
  if SyntaxEqual.equal_lval expected actual then ok
  else error (label ^ ": lvalue mismatch")

let check_instr label expected actual =
  if SyntaxEqual.equal_instr expected actual then ok
  else error (label ^ ": instruction mismatch")

let check_stmt label expected actual =
  if SyntaxEqual.equal_stmt expected actual then ok
  else error (label ^ ": statement mismatch")

let check_block label expected actual =
  if SyntaxEqual.equal_block expected actual then ok
  else error (label ^ ": block mismatch")

let check_fundec label expected actual =
  if SyntaxEqual.equal_fundec expected actual then ok
  else error (label ^ ": function mismatch")

let check_type label = function
  | Ok () -> ok
  | Error err -> error (label ^ ": " ^ TypeUtil.string_of_error err)

let check_type_value label = function
  | Ok _ -> ok
  | Error err -> error (label ^ ": " ^ TypeUtil.string_of_error err)

let check_file_result label = function
  | Ok () -> ok
  | Error err -> error (label ^ ": " ^ Check.string_of_error err)

let check_return_type label return_type exp =
  match return_type with
  | None -> ok
  | Some return_type ->
      check_type label (TypeUtil.check_return ~return_type exp)

let rec check_list check = function
  | [] -> ok
  | x :: xs -> check x >>= fun () -> check_list check xs

let rec check_etree tree =
  match tree with
  | ETreeConst (_, exp, value) -> (
      check_type_value "E-Const type" (TypeUtil.type_of_exp exp) >>= fun () ->
      match exp with
      | Syntax.Const constant -> (
          match Value.of_constant constant with
          | Ok expected -> check_value "E-Const value" expected value
          | Error err ->
              error ("E-Const evaluation failed: " ^ Value.string_of_error err)
          )
      | Syntax.UnOp (Syntax.Neg, Syntax.Const constant, _) -> (
          match Value.of_negated_constant constant with
          | Ok expected -> check_value "E-Const value" expected value
          | Error err ->
              error ("E-Const evaluation failed: " ^ Value.string_of_error err)
          )
      | _ -> error "E-Const subject is not a constant expression")
  | ETreeLval (ltree, (mem, exp, value)) ->
      check_ltree ltree >>= fun () ->
      check_type_value "E-Lval type" (TypeUtil.type_of_exp exp) >>= fun () ->
      let l_mem, lval, loc = l_concl ltree in
      check_memory "E-Lval input" mem l_mem >>= fun () ->
      check_exp "E-Lval subject" exp (Syntax.Lval lval) >>= fun () ->
      (match Memory.read loc mem with
      | Ok expected -> check_value "E-Lval value" expected value
      | Error err -> error ("E-Lval read failed: " ^ Memory.string_of_error err))
  | ETreeUnOp (sub, (mem, exp, value)) -> (
      check_etree sub >>= fun () ->
      check_type_value "E-UnOp type" (TypeUtil.type_of_exp exp) >>= fun () ->
      let sub_mem, sub_exp, sub_value = e_concl sub in
      check_memory "E-UnOp input" mem sub_mem >>= fun () ->
      match exp with
      | Syntax.UnOp (op, expected_sub_exp, _) ->
          check_exp "E-UnOp operand" expected_sub_exp sub_exp >>= fun () -> (
          match ValueOp.eval_unop op sub_value with
          | Ok expected -> check_value "E-UnOp value" expected value
          | Error err ->
              error ("E-UnOp evaluation failed: " ^ ValueOp.string_of_error err) )
      | _ -> error "E-UnOp subject is not a unary expression")
  | ETreeLogicalOrLeftTrue (left, (mem, exp, value)) -> (
      check_etree left >>= fun () ->
      check_type_value "E-LOr true type" (TypeUtil.type_of_exp exp) >>= fun () ->
      let left_mem, left_exp, left_value = e_concl left in
      check_memory "E-LOr true input" mem left_mem >>= fun () ->
      match exp with
      | Syntax.BinOp (Syntax.LOr, expected_left, _, _) ->
          check_exp "E-LOr true left" expected_left left_exp >>= fun () -> (
          match Value.truthy left_value with
          | Ok true -> check_value "E-LOr true value" (Value.of_bool true) value
          | Ok false -> error "E-LOr true has false left premise"
          | Error err ->
              error ("E-LOr true truthiness failed: " ^ Value.string_of_error err) )
      | _ -> error "E-LOr true subject is not logical-or")
  | ETreeLogicalOrLeftFalse (left, right, (mem, exp, value)) -> (
      check_etree left >>= fun () ->
      check_etree right >>= fun () ->
      check_type_value "E-LOr false type" (TypeUtil.type_of_exp exp) >>= fun () ->
      let left_mem, left_exp, left_value = e_concl left in
      let right_mem, right_exp, right_value = e_concl right in
      check_memory "E-LOr false left input" mem left_mem >>= fun () ->
      check_memory "E-LOr false right input" mem right_mem >>= fun () ->
      match exp with
      | Syntax.BinOp (Syntax.LOr, expected_left, expected_right, _) ->
          check_exp "E-LOr false left" expected_left left_exp >>= fun () ->
          check_exp "E-LOr false right" expected_right right_exp >>= fun () -> (
          match Value.truthy left_value, Value.truthy right_value with
          | Ok false, Ok right_truthy ->
              check_value "E-LOr false value" (Value.of_bool right_truthy) value
          | Ok true, _ -> error "E-LOr false has true left premise"
          | Error err, _ | _, Error err ->
              error ("E-LOr false truthiness failed: " ^ Value.string_of_error err) )
      | _ -> error "E-LOr false subject is not logical-or")
  | ETreeLogicalAndLeftFalse (left, (mem, exp, value)) -> (
      check_etree left >>= fun () ->
      check_type_value "E-LAnd false type" (TypeUtil.type_of_exp exp) >>= fun () ->
      let left_mem, left_exp, left_value = e_concl left in
      check_memory "E-LAnd false input" mem left_mem >>= fun () ->
      match exp with
      | Syntax.BinOp (Syntax.LAnd, expected_left, _, _) ->
          check_exp "E-LAnd false left" expected_left left_exp >>= fun () -> (
          match Value.truthy left_value with
          | Ok false -> check_value "E-LAnd false value" (Value.of_bool false) value
          | Ok true -> error "E-LAnd false has true left premise"
          | Error err ->
              error ("E-LAnd false truthiness failed: " ^ Value.string_of_error err) )
      | _ -> error "E-LAnd false subject is not logical-and")
  | ETreeLogicalAndLeftTrue (left, right, (mem, exp, value)) -> (
      check_etree left >>= fun () ->
      check_etree right >>= fun () ->
      check_type_value "E-LAnd true type" (TypeUtil.type_of_exp exp) >>= fun () ->
      let left_mem, left_exp, left_value = e_concl left in
      let right_mem, right_exp, right_value = e_concl right in
      check_memory "E-LAnd true left input" mem left_mem >>= fun () ->
      check_memory "E-LAnd true right input" mem right_mem >>= fun () ->
      match exp with
      | Syntax.BinOp (Syntax.LAnd, expected_left, expected_right, _) ->
          check_exp "E-LAnd true left" expected_left left_exp >>= fun () ->
          check_exp "E-LAnd true right" expected_right right_exp >>= fun () -> (
          match Value.truthy left_value, Value.truthy right_value with
          | Ok true, Ok right_truthy ->
              check_value "E-LAnd true value" (Value.of_bool right_truthy) value
          | Ok false, _ -> error "E-LAnd true has false left premise"
          | Error err, _ | _, Error err ->
              error ("E-LAnd true truthiness failed: " ^ Value.string_of_error err) )
      | _ -> error "E-LAnd true subject is not logical-and")
  | ETreeBinOp (left, right, (mem, exp, value)) -> (
      check_etree left >>= fun () ->
      check_etree right >>= fun () ->
      check_type_value "E-BinOp type" (TypeUtil.type_of_exp exp) >>= fun () ->
      let left_mem, left_exp, left_value = e_concl left in
      let right_mem, right_exp, right_value = e_concl right in
      check_memory "E-BinOp left input" mem left_mem >>= fun () ->
      check_memory "E-BinOp right input" mem right_mem >>= fun () ->
      match exp with
      | Syntax.BinOp (op, expected_left, expected_right, _) ->
          check_exp "E-BinOp left" expected_left left_exp >>= fun () ->
          check_exp "E-BinOp right" expected_right right_exp >>= fun () -> (
          match ValueOp.eval_binop op left_value right_value with
          | Ok expected -> check_value "E-BinOp value" expected value
          | Error err ->
              error ("E-BinOp evaluation failed: " ^ ValueOp.string_of_error err) )
      | _ -> error "E-BinOp subject is not a binary expression")
  | ETreeAddrOf (ltree, (mem, exp, value)) -> (
      check_ltree ltree >>= fun () ->
      check_type_value "E-AddrOf type" (TypeUtil.type_of_exp exp) >>= fun () ->
      let l_mem, lval, loc = l_concl ltree in
      check_memory "E-AddrOf input" mem l_mem >>= fun () ->
      check_exp "E-AddrOf subject" exp (Syntax.AddrOf lval) >>= fun () ->
      match value with
      | Value.Ptr actual -> check_location "E-AddrOf location" loc actual
      | Value.Int _ -> error "E-AddrOf result is not a pointer")
  | ETreeStartOf (ltree, (mem, exp, value)) -> (
      check_ltree ltree >>= fun () ->
      check_type_value "E-StartOf type" (TypeUtil.type_of_exp exp) >>= fun () ->
      let l_mem, lval, loc = l_concl ltree in
      check_memory "E-StartOf input" mem l_mem >>= fun () ->
      check_exp "E-StartOf subject" exp (Syntax.StartOf lval) >>= fun () ->
      match value with
      | Value.Ptr actual -> check_location "E-StartOf location" loc actual
      | Value.Int _ -> error "E-StartOf result is not a pointer")

and check_ltree tree =
  match tree with
  | LTreeVar (mem, lval, loc) -> (
      check_type_value "L-Var type" (TypeUtil.type_of_lval lval) >>= fun () ->
      match lval with
      | Syntax.Var var, Syntax.NoOffset -> (
          match Memory.loc_of_var var mem with
          | Ok expected -> check_location "L-Var location" expected loc
          | Error err -> error ("L-Var failed: " ^ Memory.string_of_error err) )
      | _ -> error "L-Var subject is not a variable lvalue")
  | LTreeMem (etree, (mem, lval, _loc)) ->
      check_etree etree >>= fun () ->
      check_type_value "L-Mem type" (TypeUtil.type_of_lval lval) >>= fun () ->
      let e_mem, exp, _value = e_concl etree in
      check_memory "L-Mem input" mem e_mem >>= fun () ->
      check_lval "L-Mem subject" lval (Syntax.Mem exp, snd lval)
  | LTreeIndex (base, index, (mem, _lval, _loc)) ->
      check_ltree base >>= fun () ->
      check_etree index >>= fun () ->
      check_type_value "L-Index type" (TypeUtil.type_of_lval _lval)
      >>= fun () ->
      let base_mem, _, _ = l_concl base in
      let index_mem, _, _ = e_concl index in
      check_memory "L-Index base input" mem base_mem >>= fun () ->
      check_memory "L-Index index input" mem index_mem

let rec check_itree tree =
  match tree with
  | ITreeSet (ltree, etree, (mem, instr, out_mem)) -> (
      check_ltree ltree >>= fun () ->
      check_etree etree >>= fun () ->
      let l_mem, lval, loc = l_concl ltree in
      let e_mem, exp, value = e_concl etree in
      check_memory "I-Set lvalue input" mem l_mem >>= fun () ->
      check_memory "I-Set expression input" mem e_mem >>= fun () ->
      check_type "I-Set type" (TypeUtil.check_assign lval exp) >>= fun () ->
      check_instr "I-Set subject" instr (Syntax.Set (lval, exp)) >>= fun () ->
      match Memory.write loc value mem with
      | Ok expected -> check_memory "I-Set output" expected out_mem
      | Error err -> error ("I-Set write failed: " ^ Memory.string_of_error err) )
  | ITreeCallVoid (callee, args, ftree, (mem, instr, out_mem)) -> (
      check_callee_tree callee >>= fun () ->
      check_list check_etree args >>= fun () ->
      check_ftree ftree >>= fun () ->
      let arg_values = List.map e_value args in
      let arg_exps = List.map (fun arg -> let _, exp, _ = e_concl arg in exp) args in
      let fd = callee_fundec callee in
      let f_mem, f_fd, f_args, f_out_mem, _ = f_concl ftree in
      check_memory "I-CallVoid callee input" mem f_mem >>= fun () ->
      check_fundec "I-CallVoid function" fd f_fd >>= fun () ->
      if f_args <> arg_values then error "I-CallVoid argument values mismatch"
      else
        check_type "I-CallVoid type"
          (TypeUtil.check_call ~return_target:None ~callee:(callee_exp callee)
             ~args:arg_exps)
        >>= fun () ->
        check_instr "I-CallVoid subject"
          instr
          (Syntax.Call (None, callee_exp callee, arg_exps))
        >>= fun () -> check_memory "I-CallVoid output" f_out_mem out_mem )
  | ITreeCallAssign (ltree, callee, args, ftree, (mem, instr, out_mem)) -> (
      check_ltree ltree >>= fun () ->
      check_callee_tree callee >>= fun () ->
      check_list check_etree args >>= fun () ->
      check_ftree ftree >>= fun () ->
      let l_mem, lval, loc = l_concl ltree in
      let arg_values = List.map e_value args in
      let arg_exps = List.map (fun arg -> let _, exp, _ = e_concl arg in exp) args in
      let fd = callee_fundec callee in
      let f_mem, f_fd, f_args, f_out_mem, f_control = f_concl ftree in
      check_memory "I-CallAssign lvalue input" mem l_mem >>= fun () ->
      check_memory "I-CallAssign callee input" mem f_mem >>= fun () ->
      check_fundec "I-CallAssign function" fd f_fd >>= fun () ->
      if f_args <> arg_values then error "I-CallAssign argument values mismatch"
      else
        check_type "I-CallAssign type"
          (TypeUtil.check_call ~return_target:(Some lval)
             ~callee:(callee_exp callee) ~args:arg_exps)
        >>= fun () ->
        check_instr "I-CallAssign subject"
          instr
          (Syntax.Call (Some lval, callee_exp callee, arg_exps))
        >>= fun () ->
        match f_control with
        | Return value -> (
            match Memory.write loc value f_out_mem with
            | Ok expected -> check_memory "I-CallAssign output" expected out_mem
            | Error err ->
                error ("I-CallAssign write failed: " ^ Memory.string_of_error err) )
        | ReturnVoid | Normal | Break | Continue ->
            error "I-CallAssign callee did not return a value" )

and check_callee_tree = function
  | CalleeTreeDirect (exp, var, fd) ->
      check_exp "Callee direct expression" exp (Syntax.Lval (Syntax.Var var, Syntax.NoOffset))
      >>= fun () ->
      if var.Syntax.vid = fd.Syntax.svar.Syntax.vid then ok
      else error "Callee direct var/function mismatch"

and callee_exp = function
  | CalleeTreeDirect (exp, _, _) -> exp

and check_stree ?return_type tree =
  match tree with
  | STreeInstr (itrees, (mem, stmt, out_mem, control)) ->
      check_list check_itree itrees >>= fun () ->
      check_stmt "S-Instr subject" stmt (Syntax.{ labels = []; skind = Instr (List.map (fun itree -> let _, instr, _ = i_concl itree in instr) itrees); sid = stmt.sid })
      >>= fun () ->
      let expected_out = BigStepUtil.instrs_output_memory mem itrees in
      check_memory "S-Instr output" expected_out out_mem >>= fun () ->
      check_control "S-Instr control" Normal control
  | STreeReturnNone (_mem, stmt, _out_mem, control) ->
      check_stmt "S-ReturnNone subject" stmt { stmt with Syntax.skind = Syntax.Return None }
      >>= fun () ->
      check_return_type "S-ReturnNone type" return_type None >>= fun () ->
      check_control "S-ReturnNone control" ReturnVoid control
  | STreeReturnSome (etree, (mem, stmt, out_mem, control)) ->
      check_etree etree >>= fun () ->
      let e_mem, exp, value = e_concl etree in
      check_memory "S-ReturnSome input" mem e_mem >>= fun () ->
      check_memory "S-ReturnSome output" mem out_mem >>= fun () ->
      check_return_type "S-ReturnSome type" return_type (Some exp)
      >>= fun () ->
      check_stmt "S-ReturnSome subject" stmt { stmt with Syntax.skind = Syntax.Return (Some exp) }
      >>= fun () -> check_control "S-ReturnSome control" (Return value) control
  | STreeBreak (_mem, stmt, _out_mem, control) ->
      check_stmt "S-Break subject" stmt { stmt with Syntax.skind = Syntax.Break }
      >>= fun () -> check_control "S-Break control" Break control
  | STreeContinue (_mem, stmt, _out_mem, control) ->
      check_stmt "S-Continue subject" stmt { stmt with Syntax.skind = Syntax.Continue }
      >>= fun () -> check_control "S-Continue control" Continue control
  | STreeIfTrue (cond, body, (mem, stmt, out_mem, control)) -> (
      check_etree cond >>= fun () ->
      check_btree ?return_type body >>= fun () ->
      let cond_mem, cond_exp, cond_value = e_concl cond in
      let body_mem, then_block, body_out, body_control = b_concl body in
      check_memory "S-IfTrue condition input" mem cond_mem >>= fun () ->
      check_memory "S-IfTrue body input" mem body_mem >>= fun () ->
      match stmt.Syntax.skind with
      | Syntax.If (expected_cond, expected_then, _) ->
          check_exp "S-IfTrue condition" expected_cond cond_exp >>= fun () ->
          check_block "S-IfTrue then block" expected_then then_block >>= fun () -> (
          match Value.truthy cond_value with
          | Ok true ->
              check_memory "S-IfTrue output" body_out out_mem >>= fun () ->
              check_control "S-IfTrue control" body_control control
          | Ok false -> error "S-IfTrue has false condition"
          | Error err ->
              error ("S-IfTrue truthiness failed: " ^ Value.string_of_error err) )
      | _ -> error "S-IfTrue subject is not if")
  | STreeIfFalse (cond, body, (mem, stmt, out_mem, control)) -> (
      check_etree cond >>= fun () ->
      check_btree ?return_type body >>= fun () ->
      let cond_mem, cond_exp, cond_value = e_concl cond in
      let body_mem, else_block, body_out, body_control = b_concl body in
      check_memory "S-IfFalse condition input" mem cond_mem >>= fun () ->
      check_memory "S-IfFalse body input" mem body_mem >>= fun () ->
      match stmt.Syntax.skind with
      | Syntax.If (expected_cond, _, expected_else) ->
          check_exp "S-IfFalse condition" expected_cond cond_exp >>= fun () ->
          check_block "S-IfFalse else block" expected_else else_block >>= fun () -> (
          match Value.truthy cond_value with
          | Ok false ->
              check_memory "S-IfFalse output" body_out out_mem >>= fun () ->
              check_control "S-IfFalse control" body_control control
          | Ok true -> error "S-IfFalse has true condition"
          | Error err ->
              error ("S-IfFalse truthiness failed: " ^ Value.string_of_error err) )
      | _ -> error "S-IfFalse subject is not if")
  | STreeLoopRepeat (body, rest, (mem, stmt, out_mem, control))
  | STreeLoopContinue (body, rest, (mem, stmt, out_mem, control)) ->
      check_btree ?return_type body >>= fun () ->
      check_stree ?return_type rest >>= fun () ->
      let body_mem, body_block, body_out, _ = b_concl body in
      let rest_mem, rest_stmt, rest_out, rest_control = s_concl rest in
      check_memory "S-Loop recursive body input" mem body_mem >>= fun () ->
      check_memory "S-Loop recursive rest input" body_out rest_mem >>= fun () ->
      check_stmt "S-Loop recursive rest subject" stmt rest_stmt >>= fun () ->
      check_memory "S-Loop recursive output" rest_out out_mem >>= fun () ->
      check_control "S-Loop recursive control" rest_control control >>= fun () ->
      (match stmt.Syntax.skind with
      | Syntax.Loop expected_body -> check_block "S-Loop body" expected_body body_block
      | _ -> error "S-Loop subject is not loop")
  | STreeLoopBreak (body, (mem, stmt, out_mem, control)) ->
      check_btree ?return_type body >>= fun () ->
      let body_mem, body_block, body_out, body_control = b_concl body in
      check_memory "S-LoopBreak body input" mem body_mem >>= fun () ->
      check_memory "S-LoopBreak output" body_out out_mem >>= fun () ->
      check_control "S-LoopBreak body control" Break body_control >>= fun () ->
      check_control "S-LoopBreak control" Normal control >>= fun () ->
      (match stmt.Syntax.skind with
      | Syntax.Loop expected_body -> check_block "S-LoopBreak body" expected_body body_block
      | _ -> error "S-LoopBreak subject is not loop")
  | STreeLoopReturn (body, (mem, stmt, out_mem, control)) ->
      check_btree ?return_type body >>= fun () ->
      let body_mem, body_block, body_out, body_control = b_concl body in
      check_memory "S-LoopReturn body input" mem body_mem >>= fun () ->
      check_memory "S-LoopReturn output" body_out out_mem >>= fun () ->
      check_control "S-LoopReturn control" body_control control >>= fun () ->
      if is_return body_control then
        (match stmt.Syntax.skind with
        | Syntax.Loop expected_body ->
            check_block "S-LoopReturn body" expected_body body_block
        | _ -> error "S-LoopReturn subject is not loop")
      else error "S-LoopReturn body did not return"
  | STreeBlock (body, (mem, stmt, out_mem, control)) ->
      check_btree ?return_type body >>= fun () ->
      let body_mem, block, body_out, body_control = b_concl body in
      check_memory "S-Block input" mem body_mem >>= fun () ->
      check_memory "S-Block output" body_out out_mem >>= fun () ->
      check_control "S-Block control" body_control control >>= fun () ->
      check_stmt "S-Block subject" stmt { stmt with Syntax.skind = Syntax.Block block }

and check_btree ?return_type tree =
  match tree with
  | BTreeSeq (strees, (mem, block, out_mem, control)) ->
      check_list (check_stree ?return_type) strees >>= fun () ->
      check_block_flow ?return_type mem strees >>= fun () ->
      let expected_out =
        match List.rev strees with
        | [] -> mem
        | last :: _ -> s_output_memory last
      in
      let expected_control =
        match List.rev strees with
        | [] -> Normal
        | last :: _ -> s_control last
      in
      check_memory "B-Seq output" expected_out out_mem >>= fun () ->
      check_control "B-Seq control" expected_control control >>= fun () ->
      if List.length strees <= List.length block.Syntax.bstmts then ok
      else error "B-Seq executed more statements than block contains"

and check_block_flow ?return_type mem = function
  | [] -> ok
  | stree :: strees ->
      let s_mem, _, s_out, s_control = s_concl stree in
      check_memory "B-Seq statement input" mem s_mem >>= fun () ->
      if s_control = Normal then check_block_flow ?return_type s_out strees
      else if strees = [] then ok
      else error "B-Seq has statements after non-normal control"

and check_ftree tree =
  match tree with
  | FTreeReturn (btree, (mem, fd, _args, out_mem, control))
  | FTreeNoReturn (btree, (mem, fd, _args, out_mem, control)) ->
      check_btree ~return_type:(SyntaxUtil.function_return_type fd) btree
      >>= fun () ->
      let _body_mem, body, body_out, body_control = b_concl btree in
      check_block "F body" fd.Syntax.sbody body >>= fun () ->
      (match Memory.leave_function body_out with
      | Ok expected -> check_memory "F output" expected out_mem
      | Error err -> error ("F leave function failed: " ^ Memory.string_of_error err))
      >>= fun () ->
      check_control "F control" body_control control >>= fun () ->
      ignore mem;
      ok

let check_ptree ?(check_file = true) = function
  | PTreeMainReturn (ftree, (file, mem, value)) ->
      (if check_file then check_file_result "P-File" (Check.check_file file)
       else ok)
      >>= fun () ->
      (match SyntaxUtil.main_functions file with
      | [] -> error "P-Main missing main function"
      | _ :: _ :: _ -> error "P-Main has multiple main functions"
      | [ main ] ->
          let _, fd, args, _, _ = f_concl ftree in
          check_fundec "P-Main function" main fd >>= fun () ->
          if args = [] then ok else error "P-Main arguments mismatch")
      >>= fun () ->
      check_ftree ftree >>= fun () ->
      let f_out_mem = f_output_memory ftree in
      check_memory "P-Main output" f_out_mem mem >>= fun () ->
      match f_control ftree with
      | Return expected -> check_value "P-Main value" expected value
      | ReturnVoid | Normal | Break | Continue -> error "P-Main did not return a value"

let check_tree = function
  | ETree etree -> check_etree etree
  | LTree ltree -> check_ltree ltree
  | ITree itree -> check_itree itree
  | STree stree -> check_stree stree
  | BTree btree -> check_btree btree
  | FTree ftree -> check_ftree ftree
  | PTree ptree -> check_ptree ptree

let string_of_result = function
  | Valid -> "ok"
  | Invalid msg -> msg
