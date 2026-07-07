open Language

module S = Syntax
module B = BigStep
module C = BigStepChecker
module U = BigStepUtil

let int_t = Typ.TInt Typ.IInt
let uint_t = Typ.TInt Typ.IUInt
let void_t = Typ.TVoid
let mem0 = Memory.empty

let contains haystack needle =
  let hlen = String.length haystack in
  let nlen = String.length needle in
  let rec loop i =
    if nlen = 0 then true
    else if i + nlen > hlen then false
    else if String.sub haystack i nlen = needle then true
    else loop (i + 1)
  in
  loop 0

let must_ok label string_of_error = function
  | Ok value -> value
  | Error err -> failwith (label ^ ": " ^ string_of_error err)

let must_value_kind ikind n =
  match Value.of_int64 ikind (Int64.of_int n) with
  | Ok value -> value
  | Error err -> failwith ("value: " ^ Value.string_of_error err)

let must_value n = must_value_kind Typ.IInt n
let must_uint_value n = must_value_kind Typ.IUInt n

let var ?(vglob = false) ?(vtemp = false) name typ vid =
  { S.vname = name; vtype = typ; vglob; vtemp; vid }

let stmt skind = { S.labels = []; skind; sid = None }
let block bstmts = { S.bstmts }
let file globals = { S.fileName = "bigstepcheck-test.c"; globals }
let int_exp n = S.Const (S.CInt (Int64.of_int n, Typ.IInt))
let uint_exp n = S.Const (S.CInt (Int64.of_int n, Typ.IUInt))
let int_tree n = B.ETreeConst (mem0, int_exp n, must_value n)
let bad_loc = { Location.obj = Location.Stack 999; offset = 0 }
let source_root = Option.value (Sys.getenv_opt "DUNE_SOURCEROOT") ~default:(Sys.getcwd ())
let example_path name = Filename.concat source_root ("examples/" ^ name)

let expect_valid name result =
  match result with
  | C.Valid -> Printf.printf "ok - %s\n" name
  | C.Invalid msg -> failwith (Printf.sprintf "%s: expected Valid, got %s" name msg)

let expect_invalid name needle result =
  match result with
  | C.Invalid msg when contains msg needle ->
      Printf.printf "ok - %s -> %s\n" name msg
  | C.Invalid msg ->
      failwith
        (Printf.sprintf "%s: expected message containing %S, got %S" name
           needle msg)
  | C.Valid ->
      failwith (Printf.sprintf "%s: expected Invalid containing %S" name needle)

let suspected_gap_failures = ref []

let expect_suspected_gap_invalid name needle result =
  match result with
  | C.Invalid msg when contains msg needle ->
      Printf.printf "ok - %s -> %s\n" name msg
  | C.Invalid msg ->
      suspected_gap_failures :=
        (Printf.sprintf "%s: expected message containing %S, got %S" name
           needle msg)
        :: !suspected_gap_failures;
      Printf.printf "not ok - %s -> wrong error: %s\n" name msg
  | C.Valid ->
      suspected_gap_failures :=
        (Printf.sprintf "%s: expected Invalid containing %S, got Valid" name
           needle)
        :: !suspected_gap_failures;
      Printf.printf "not ok - %s -> accepted invalid proof\n" name

let parse_example path =
  match CilBridge.parse_c_file_as_file path with
  | Ok file -> file
  | Error err -> failwith (path ^ ": " ^ CilBridge.string_of_error err)

let derive_example path =
  let file = parse_example path in
  begin
    match Check.check_file file with
    | Ok () -> ()
    | Error err -> failwith (path ^ ": " ^ Check.string_of_error err)
  end;
  match Derivator.derive_file file with
  | Ok tree -> tree
  | Error err -> failwith (path ^ ": " ^ Derivator.string_of_error err)

let expect_valid_example path =
  let tree = derive_example path in
  expect_valid ("accept_" ^ Filename.basename path)
    (C.check_ptree ~use_check_file:false tree)

let local_binding ?(typ = int_t) ?(value = must_value 1) name vid =
  let x = var name typ vid in
  let lval = (S.Var x, S.NoOffset) in
  let loc, mem =
    must_ok "bind local" Memory.string_of_error
      (Memory.bind_local x value (Memory.enter_function Memory.empty))
  in
  (x, lval, loc, mem)

let valid_ltree () =
  let _, lval, loc, mem = local_binding "x" 10 in
  B.LTreeVar (mem, lval, loc)

let valid_set_itree () =
  let _, lval, loc, mem = local_binding "x" 11 in
  let exp = int_exp 2 in
  let value = must_value 2 in
  let etree = B.ETreeConst (mem, exp, value) in
  let out_mem = must_ok "write" Memory.string_of_error (Memory.write loc value mem) in
  B.ITreeSet (B.LTreeVar (mem, lval, loc), etree, (mem, S.Set (lval, exp), out_mem))

let valid_return_stree () =
  let exp = int_exp 1 in
  let value = must_value 1 in
  let etree = B.ETreeConst (mem0, exp, value) in
  B.STreeReturnSome (etree, (mem0, stmt (S.Return (Some exp)), mem0, B.Return value))

let empty_btree mem =
  let b = block [] in
  B.BTreeSeq ([], (mem, b, mem, B.Normal))

let minimal_main body =
  {
    S.svar = var ~vglob:true "main" int_t 1;
    sformals = [];
    slocals = [];
    sbody = body;
  }

let mutate_main_ftree f tree =
  match tree with
  | B.PTreeMainReturn (ftree, concl) -> B.PTreeMainReturn (f ftree, concl)

let mutate_main_concl f tree =
  match tree with
  | B.PTreeMainReturn (ftree, concl) -> B.PTreeMainReturn (ftree, f concl)

let first_call_assign tree =
  match tree with
  | B.PTreeMainReturn
      ( B.FTreeReturn (B.BTreeSeq (B.STreeInstr ([ itree ], _) :: _, _), _),
        _ ) -> (
      match itree with
      | B.ITreeCallAssign _ -> itree
      | _ -> failwith "first instruction is not a call assignment" )
  | _ -> failwith "unexpected function_call proof shape"

let call_with_callee_var callee_var itree =
  match itree with
  | B.ITreeCallAssign (ltree, B.CalleeTreeDirect (_, _, fd), args, ftree, concl) ->
      let callee_exp = S.Lval (S.Var callee_var, S.NoOffset) in
      B.ITreeCallAssign
        (ltree, B.CalleeTreeDirect (callee_exp, callee_var, fd), args, ftree, concl)
  | _ -> failwith "expected call assignment tree"

let call_with_first_arg_mem mem itree =
  match itree with
  | B.ITreeCallAssign (ltree, callee, arg :: args, ftree, concl) ->
      let arg =
        match arg with
        | B.ETreeConst (_, exp, value) -> B.ETreeConst (mem, exp, value)
        | _ -> failwith "expected constant call argument"
      in
      B.ITreeCallAssign (ltree, callee, arg :: args, ftree, concl)
  | _ -> failwith "expected call assignment tree with arguments"

let call_with_forged_callee_signature itree =
  match itree with
  | B.ITreeCallAssign
      (ltree, B.CalleeTreeDirect (_, var, fd), args, _ftree, concl) ->
      let call_mem, instr, _ = concl in
      let _, _, ret_loc = U.l_concl ltree in
      let arg_values = List.map U.e_value args in
      let forged_var = { var with S.vtype = Typ.TFun (int_t, Some [ ("x", int_t) ]) } in
      let forged_formal =
        match fd.S.sformals with
        | formal :: _ -> { formal with S.vtype = uint_t }
        | [] -> failwith "expected one formal"
      in
      let return_stmt = stmt (S.Return (Some (int_exp 1))) in
      let forged_fd =
        { fd with S.sformals = [ forged_formal ]; sbody = block [ return_stmt ] }
      in
      let body_mem =
        must_ok "forged body input" Memory.string_of_error
          (Memory.bind_local forged_formal (List.hd arg_values)
             (Memory.enter_function call_mem))
        |> snd
      in
      let forged_body =
        let exp = int_exp 1 in
        let value = must_value 1 in
        let return_tree =
          B.STreeReturnSome
            ( B.ETreeConst (body_mem, exp, value),
              (body_mem, stmt (S.Return (Some exp)), body_mem, B.Return value)
            )
        in
        B.BTreeSeq
          ([ return_tree ], (body_mem, forged_fd.S.sbody, body_mem, B.Return value))
      in
      let forged_out =
        must_ok "forged leave function" Memory.string_of_error
          (Memory.leave_function body_mem)
      in
      let forged_call_out =
        must_ok "forged call write" Memory.string_of_error
          (Memory.write ret_loc (must_value 1) forged_out)
      in
      let forged_ftree =
        B.FTreeReturn
          (forged_body, (call_mem, forged_fd, arg_values, forged_out, B.Return (must_value 1)))
      in
      let callee_exp = S.Lval (S.Var forged_var, S.NoOffset) in
      B.ITreeCallAssign
        ( ltree,
          B.CalleeTreeDirect (callee_exp, forged_var, forged_fd),
          args,
          forged_ftree,
          (call_mem, instr, forged_call_out) )
  | _ -> failwith "expected call assignment tree"

let call_void_with_forged_callee_signature itree =
  match itree with
  | B.ITreeCallAssign
      (_, B.CalleeTreeDirect (_, var, fd), args, _ftree, concl) ->
      let call_mem, _, _ = concl in
      let arg_values = List.map U.e_value args in
      let arg_exps = List.map (fun arg -> let _, exp, _ = U.e_concl arg in exp) args in
      let forged_var = { var with S.vtype = Typ.TFun (int_t, Some [ ("x", int_t) ]) } in
      let forged_formal =
        match fd.S.sformals with
        | formal :: _ -> { formal with S.vtype = uint_t }
        | [] -> failwith "expected one formal"
      in
      let return_stmt = stmt (S.Return (Some (int_exp 1))) in
      let forged_fd =
        { fd with S.sformals = [ forged_formal ]; sbody = block [ return_stmt ] }
      in
      let body_mem =
        must_ok "forged void body input" Memory.string_of_error
          (Memory.bind_local forged_formal (List.hd arg_values)
             (Memory.enter_function call_mem))
        |> snd
      in
      let forged_body =
        let exp = int_exp 1 in
        let value = must_value 1 in
        let return_tree =
          B.STreeReturnSome
            ( B.ETreeConst (body_mem, exp, value),
              (body_mem, stmt (S.Return (Some exp)), body_mem, B.Return value)
            )
        in
        B.BTreeSeq
          ([ return_tree ], (body_mem, forged_fd.S.sbody, body_mem, B.Return value))
      in
      let forged_out =
        must_ok "forged void leave function" Memory.string_of_error
          (Memory.leave_function body_mem)
      in
      let forged_ftree =
        B.FTreeReturn
          (forged_body, (call_mem, forged_fd, arg_values, forged_out, B.Return (must_value 1)))
      in
      let callee_exp = S.Lval (S.Var forged_var, S.NoOffset) in
      B.ITreeCallVoid
        ( B.CalleeTreeDirect (callee_exp, forged_var, forged_fd),
          args,
          forged_ftree,
          (call_mem, S.Call (None, callee_exp, arg_exps), forged_out) )
  | _ -> failwith "expected call assignment tree"

let return_const_stree mem n =
  let exp = int_exp n in
  let value = must_value n in
  B.STreeReturnSome
    (B.ETreeConst (mem, exp, value), (mem, stmt (S.Return (Some exp)), mem, B.Return value))

let break_btree mem =
  let break_stmt = stmt S.Break in
  B.BTreeSeq
    ([ B.STreeBreak (mem, break_stmt, mem, B.Break) ],
     (mem, block [ break_stmt ], mem, B.Break))

let run_expression_errors () =
  expect_invalid "reject_const_value" "E-Const value"
    (C.check_etree (B.ETreeConst (mem0, int_exp 1, must_value 2)));
  let x, lval, _, _ = local_binding "x" 20 in
  ignore x;
  expect_invalid "reject_const_subject" "E-Const subject"
    (C.check_etree (B.ETreeConst (mem0, S.Lval lval, must_value 1)));
  let ltree = valid_ltree () in
  let mem, lval, _ = U.l_concl ltree in
  expect_invalid "reject_lval_subject" "E-Lval subject"
    (C.check_etree (B.ETreeLval (ltree, (mem, int_exp 0, must_value 1))));
  expect_invalid "reject_lval_value" "E-Lval value"
    (C.check_etree (B.ETreeLval (ltree, (mem, S.Lval lval, must_value 2))));
  expect_invalid "reject_unop_type" "unsupported unary operator"
    (C.check_etree
       (B.ETreeUnOp
          (int_tree 1, (mem0, S.UnOp (S.BNot, int_exp 1, int_t), must_value 0))));
  expect_invalid "reject_unop_operand" "E-UnOp operand"
    (C.check_etree
       (B.ETreeUnOp
          (int_tree 1, (mem0, S.UnOp (S.Neg, int_exp 2, int_t), must_value (-2)))));
  expect_invalid "reject_unop_value" "E-UnOp value"
    (C.check_etree
       (B.ETreeUnOp
          (int_tree 1, (mem0, S.UnOp (S.Neg, int_exp 1, int_t), must_value 99))));
  expect_invalid "reject_binop_type" "unsupported binary operator"
    (C.check_etree
       (B.ETreeBinOp
          ( int_tree 1,
            int_tree 2,
            (mem0, S.BinOp (S.BAnd, int_exp 1, int_exp 2, int_t), must_value 0)
          )));
  expect_invalid "reject_binop_left" "E-BinOp left"
    (C.check_etree
       (B.ETreeBinOp
          ( int_tree 1,
            int_tree 2,
            (mem0, S.BinOp (S.PlusA, int_exp 9, int_exp 2, int_t), must_value 3)
          )));
  expect_invalid "reject_binop_value" "E-BinOp value"
    (C.check_etree
       (B.ETreeBinOp
          ( int_tree 1,
            int_tree 2,
            (mem0, S.BinOp (S.PlusA, int_exp 1, int_exp 2, int_t), must_value 99)
          )));
  expect_invalid "reject_binop_logical_constructor" "E-BinOp logical operator"
    (C.check_etree
       (B.ETreeBinOp
          ( int_tree 1,
            int_tree 2,
            (mem0, S.BinOp (S.LAnd, int_exp 1, int_exp 2, int_t), Value.of_bool true)
          )));
  expect_invalid "reject_lor_true_premise" "false left premise"
    (C.check_etree
       (B.ETreeLogicalOrLeftTrue
          (int_tree 0, (mem0, S.BinOp (S.LOr, int_exp 0, int_exp 1, int_t), Value.of_bool true))));
  expect_invalid "reject_lor_false_premise" "true left premise"
    (C.check_etree
       (B.ETreeLogicalOrLeftFalse
          ( int_tree 1,
            int_tree 0,
            (mem0, S.BinOp (S.LOr, int_exp 1, int_exp 0, int_t), Value.of_bool false)
          )));
  expect_invalid "reject_land_false_premise" "true left premise"
    (C.check_etree
       (B.ETreeLogicalAndLeftFalse
          (int_tree 1, (mem0, S.BinOp (S.LAnd, int_exp 1, int_exp 0, int_t), Value.of_bool false))));
  expect_invalid "reject_land_true_premise" "false left premise"
    (C.check_etree
       (B.ETreeLogicalAndLeftTrue
          ( int_tree 0,
            int_tree 1,
            (mem0, S.BinOp (S.LAnd, int_exp 0, int_exp 1, int_t), Value.of_bool false)
          )));
  expect_invalid "reject_addrof_unsupported" "unsupported expression"
    (C.check_etree (B.ETreeAddrOf (ltree, (mem, S.AddrOf lval, Value.ptr bad_loc))))

let run_lvalue_errors () =
  let x = var "x" int_t 30 in
  expect_invalid "reject_ltree_var_unbound" "L-Var failed"
    (C.check_ltree (B.LTreeVar (mem0, (S.Var x, S.NoOffset), bad_loc)));
  expect_invalid "reject_ltree_mem_unsupported" "unsupported lvalue"
    (C.check_ltree
       (B.LTreeMem
          (int_tree 1, (mem0, (S.Mem (int_exp 1), S.NoOffset), bad_loc))));
  expect_invalid "reject_ltree_index_unsupported" "unsupported lvalue"
    (C.check_ltree
       (B.LTreeIndex
          ( valid_ltree (),
            int_tree 0,
            (mem0, (S.Var x, S.Index (int_exp 0, S.NoOffset)), bad_loc) )))

let run_instruction_and_call_errors () =
  let set_tree = valid_set_itree () in
  begin
    match set_tree with
    | B.ITreeSet (ltree, _, (mem, S.Set (lval, _), out_mem)) ->
        let etree = B.ETreeConst (mem, uint_exp 1, must_uint_value 1) in
        expect_invalid "reject_set_type" "I-Set type"
          (C.check_itree (B.ITreeSet (ltree, etree, (mem, S.Set (lval, uint_exp 1), out_mem))));
        let int_etree = B.ETreeConst (mem, int_exp 2, must_value 2) in
        expect_invalid "reject_set_subject" "I-Set subject"
          (C.check_itree (B.ITreeSet (ltree, int_etree, (mem, S.Set (lval, int_exp 9), out_mem))))
    | _ -> failwith "expected set tree"
  end;
  let call_tree = first_call_assign (derive_example (example_path "function_call.c")) in
  let callee_vid =
    match call_tree with
    | B.ITreeCallAssign (_, B.CalleeTreeDirect (_, _, fd), _, _, _) -> fd.S.svar.S.vid
    | _ -> assert false
  in
  let callee typ = var ~vglob:true "f" typ callee_vid in
  let one_param = Some [ ("x", int_t) ] in
  expect_invalid "reject_call_callee_varinfo_mismatch" "Callee direct: var/function mismatch"
    (C.check_itree
       (call_with_callee_var
          (var ~vglob:true "g" (Typ.TFun (int_t, one_param)) callee_vid)
          call_tree));
  expect_invalid "reject_call_expected_function" "expected function callee"
    (C.check_itree (call_with_callee_var (callee int_t) call_tree));
  expect_invalid "reject_call_without_parameter_types" "function without parameter types"
    (C.check_itree (call_with_callee_var (callee (Typ.TFun (int_t, None))) call_tree));
  expect_invalid "reject_call_arity" "arity mismatch"
    (C.check_itree
       (call_with_callee_var
          (callee (Typ.TFun (int_t, Some [ ("x", int_t); ("y", int_t) ])))
          call_tree));
  expect_invalid "reject_call_arg_type" "type mismatch"
    (C.check_itree
       (call_with_callee_var (callee (Typ.TFun (int_t, Some [ ("x", uint_t) ])))
          call_tree));
  expect_invalid "reject_call_assigning_void" "assigning void call result"
    (C.check_itree
       (call_with_callee_var (callee (Typ.TFun (void_t, one_param))) call_tree));
  expect_invalid "reject_call_arg_input" "I-CallAssign argument input"
    (C.check_itree (call_with_first_arg_mem (Memory.enter_function mem0) call_tree))

let run_statement_and_block_errors () =
  expect_invalid "reject_return_none_type" "S-ReturnNone type"
    (C.check_stree ~return_type:int_t
       (B.STreeReturnNone (mem0, stmt (S.Return None), mem0, B.ReturnVoid)));
  expect_invalid "reject_return_some_type" "S-ReturnSome type"
    (C.check_stree ~return_type:void_t (valid_return_stree ()));
  expect_invalid "reject_return_some_subject" "S-ReturnSome subject"
    (C.check_stree ~return_type:int_t
       (B.STreeReturnSome
          (int_tree 1, (mem0, stmt (S.Return (Some (int_exp 2))), mem0, B.Return (must_value 1)))));
  expect_invalid "reject_return_none_output" "S-ReturnNone output"
    (C.check_stree
       (B.STreeReturnNone
          (mem0, stmt (S.Return None), Memory.enter_function mem0, B.ReturnVoid)));
  expect_invalid "reject_break_output" "S-Break output"
    (C.check_stree
       (B.STreeBreak
          (mem0, stmt S.Break, Memory.enter_function mem0, B.Break)));
  expect_invalid "reject_continue_output" "S-Continue output"
    (C.check_stree
       (B.STreeContinue
          (mem0, stmt S.Continue, Memory.enter_function mem0, B.Continue)));
  let body = empty_btree mem0 in
  expect_invalid "reject_if_true_false_condition" "false condition"
    (C.check_stree
       (B.STreeIfTrue
          ( int_tree 0,
            body,
            (mem0, stmt (S.If (int_exp 0, block [], block [])), mem0, B.Normal)
          )));
  expect_invalid "reject_if_false_true_condition" "true condition"
    (C.check_stree
       (B.STreeIfFalse
          ( int_tree 1,
            body,
            (mem0, stmt (S.If (int_exp 1, block [], block [])), mem0, B.Normal)
          )));
  let ret = valid_return_stree () in
  let instr_stmt = B.STreeInstr ([], (mem0, stmt (S.Instr []), mem0, B.Normal)) in
  let wrong_prefix_block = block [ stmt (S.Return (Some (int_exp 2))) ] in
  expect_invalid "reject_block_prefix_statement" "B-Seq prefix statement"
    (C.check_btree
       (B.BTreeSeq
          ([ ret ], (mem0, wrong_prefix_block, mem0, B.Return (must_value 1)))));
  expect_invalid "reject_block_stopped_normal" "stopped before end of block"
    (C.check_btree
       (B.BTreeSeq
          ( [ instr_stmt ],
            ( mem0,
              block [ stmt (S.Instr []); stmt (S.Return (Some (int_exp 0))) ],
              mem0,
              B.Normal ) )));
  let set1 = valid_set_itree () in
  let set2 = valid_set_itree () in
  let set1_mem, instr1, _ = U.i_concl set1 in
  let _, instr2, set2_out = U.i_concl set2 in
  expect_invalid "reject_instr_flow" "S-Instr instruction input"
    (C.check_stree
       (B.STreeInstr
          ([ set1; set2 ], (set1_mem, stmt (S.Instr [ instr1; instr2 ]), set2_out, B.Normal))));
  expect_invalid "reject_block_after_return" "after non-normal control"
    (C.check_btree (B.BTreeSeq ([ ret; instr_stmt ], (mem0, block [ stmt (S.Return (Some (int_exp 1))) ], mem0, B.Return (must_value 1)))));
  expect_invalid "reject_block_too_many_statements" "more statements"
    (C.check_btree (B.BTreeSeq ([ instr_stmt ], (mem0, block [], mem0, B.Normal))))

let run_function_and_program_errors () =
  let valid = derive_example (example_path "simple.c") in
  let bad_output =
    mutate_main_ftree
      (function
        | B.FTreeReturn (btree, (mem, fd, args, _, control)) ->
            B.FTreeReturn (btree, (mem, fd, args, mem0, control))
        | tree -> tree)
      valid
  in
  expect_invalid "reject_function_output" "F output"
    (C.check_ptree ~use_check_file:false bad_output);
  let bad_control =
    mutate_main_ftree
      (function
        | B.FTreeReturn (btree, (mem, fd, args, out_mem, _)) ->
            B.FTreeReturn (btree, (mem, fd, args, out_mem, B.Normal))
        | tree -> tree)
      valid
  in
  expect_invalid "reject_function_control" "F control"
    (C.check_ptree ~use_check_file:false bad_control);
  let bad_body_input =
    match valid with
    | B.PTreeMainReturn (B.FTreeReturn (btree, (mem, fd, args, out_mem, control)), _) ->
        B.FTreeReturn
          (btree, (Memory.enter_function mem, fd, args, out_mem, control))
    | _ -> failwith "unexpected simple proof shape"
  in
  expect_invalid "reject_function_body_input" "F body input"
    (C.check_ftree bad_body_input);
  let bad_p_output =
    mutate_main_concl (fun (file, _, value) -> (file, mem0, value)) valid
  in
  expect_invalid "reject_program_output" "P-Main output"
    (C.check_ptree ~use_check_file:false bad_p_output);
  let bad_p_value =
    mutate_main_concl (fun (file, mem, _) -> (file, mem, must_value 99)) valid
  in
  expect_invalid "reject_program_value" "P-Main value"
    (C.check_ptree ~use_check_file:false bad_p_value);
  let no_main_file = file [] in
  let bad_file = mutate_main_concl (fun (_, mem, value) -> (no_main_file, mem, value)) valid in
  expect_invalid "reject_program_file" "missing main function" (C.check_ptree bad_file);
  let other_main = minimal_main (block [ stmt (S.Return (Some (int_exp 0))) ]) in
  let mismatch_file =
    file [ S.GFun { other_main with S.svar = var ~vglob:true "main" int_t 999 } ]
  in
  let bad_main =
    mutate_main_concl (fun (_, mem, value) -> (mismatch_file, mem, value)) valid
  in
  expect_invalid "reject_program_main_function" "P-Main function"
    (C.check_ptree ~use_check_file:false bad_main);
  let no_return =
    let fd = minimal_main (block []) in
    let body_mem = Memory.enter_function mem0 in
    let btree = B.BTreeSeq ([], (body_mem, fd.S.sbody, body_mem, B.Normal)) in
    let out_mem =
      must_ok "leave function" Memory.string_of_error
        (Memory.leave_function body_mem)
    in
    B.PTreeMainReturn
      (B.FTreeNoReturn (btree, (mem0, fd, [], out_mem, B.Normal)),
       (file [ S.GFun fd ], out_mem, must_value 0))
  in
  expect_invalid "reject_program_no_return" "F no-return type"
    (C.check_tree (B.PTree no_return))

let run_suspected_gap_errors () =
  let make_set_zero_stree lval loc mem =
    let exp = int_exp 0 in
    let value = must_value 0 in
    let instr = S.Set (lval, exp) in
    let etree = B.ETreeConst (mem, exp, value) in
    let ltree = B.LTreeVar (mem, lval, loc) in
    let out_mem =
      must_ok "write zero" Memory.string_of_error
        (Memory.write loc value mem)
    in
    ( B.STreeInstr ([ B.ITreeSet (ltree, etree, (mem, instr, out_mem)) ],
        (mem, stmt (S.Instr [ instr ]), out_mem, B.Normal)),
      out_mem )
  in
  let x, x_lval, x_loc, x_one_mem = local_binding "x" 90 in
  ignore x;
  let cond_exp = S.Lval x_lval in
  let set_zero_from_one, x_zero_mem = make_set_zero_stree x_lval x_loc x_one_mem in
  let set_zero_stmt =
    let _, stmt, _, _ = U.s_concl set_zero_from_one in
    stmt
  in
  let continue_stmt = stmt S.Continue in
  let break_stmt = stmt S.Break in
  let else_break_block = block [ break_stmt ] in
  let else_break_body = break_btree x_zero_mem in
  let continue_then_block = block [ set_zero_stmt; continue_stmt ] in
  let continue_then_body =
    B.BTreeSeq
      ( [ set_zero_from_one;
          B.STreeContinue (x_zero_mem, continue_stmt, x_zero_mem, B.Continue)
        ],
        (x_one_mem, continue_then_block, x_zero_mem, B.Continue) )
  in
  let continue_if_stmt =
    stmt (S.If (cond_exp, continue_then_block, else_break_block))
  in
  let continue_loop_body_block = block [ continue_if_stmt ] in
  let continue_body =
    B.BTreeSeq
      ( [ B.STreeIfTrue
            ( B.ETreeLval
                ( B.LTreeVar (x_one_mem, x_lval, x_loc),
                  (x_one_mem, cond_exp, must_value 1) ),
              continue_then_body,
              (x_one_mem, continue_if_stmt, x_zero_mem, B.Continue) )
        ],
        (x_one_mem, continue_loop_body_block, x_zero_mem, B.Continue) )
  in
  let continue_break_body =
    B.BTreeSeq
      ( [ B.STreeIfFalse
            ( B.ETreeLval
                ( B.LTreeVar (x_zero_mem, x_lval, x_loc),
                  (x_zero_mem, cond_exp, must_value 0) ),
              else_break_body,
              (x_zero_mem, continue_if_stmt, x_zero_mem, B.Break) )
        ],
        (x_zero_mem, continue_loop_body_block, x_zero_mem, B.Break) )
  in
  let continue_loop_stmt = stmt (S.Loop continue_loop_body_block) in
  let continue_loop_rest =
    B.STreeLoopBreak
      (continue_break_body, (x_zero_mem, continue_loop_stmt, x_zero_mem, B.Normal))
  in
  expect_suspected_gap_invalid "reject_loop_repeat_continue_body"
    "S-LoopRepeat body control"
    (C.check_stree
       (B.STreeLoopRepeat
          ( continue_body,
            continue_loop_rest,
            (x_one_mem, continue_loop_stmt, x_zero_mem, B.Normal) )));
  let y, y_lval, y_loc, y_one_mem = local_binding "y" 91 in
  ignore y;
  let normal_cond_exp = S.Lval y_lval in
  let set_zero_from_y_one, y_zero_mem =
    make_set_zero_stree y_lval y_loc y_one_mem
  in
  let normal_set_zero_stmt =
    let _, stmt, _, _ = U.s_concl set_zero_from_y_one in
    stmt
  in
  let normal_then_block = block [ normal_set_zero_stmt ] in
  let normal_then_body =
    B.BTreeSeq
      ([ set_zero_from_y_one ], (y_one_mem, normal_then_block, y_zero_mem, B.Normal))
  in
  let normal_if_stmt =
    stmt (S.If (normal_cond_exp, normal_then_block, else_break_block))
  in
  let normal_loop_body_block = block [ normal_if_stmt ] in
  let normal_body =
    B.BTreeSeq
      ( [ B.STreeIfTrue
            ( B.ETreeLval
                ( B.LTreeVar (y_one_mem, y_lval, y_loc),
                  (y_one_mem, normal_cond_exp, must_value 1) ),
              normal_then_body,
              (y_one_mem, normal_if_stmt, y_zero_mem, B.Normal) )
        ],
        (y_one_mem, normal_loop_body_block, y_zero_mem, B.Normal) )
  in
  let normal_break_body =
    let else_break_body = break_btree y_zero_mem in
    B.BTreeSeq
      ( [ B.STreeIfFalse
            ( B.ETreeLval
                ( B.LTreeVar (y_zero_mem, y_lval, y_loc),
                  (y_zero_mem, normal_cond_exp, must_value 0) ),
              else_break_body,
              (y_zero_mem, normal_if_stmt, y_zero_mem, B.Break) )
        ],
        (y_zero_mem, normal_loop_body_block, y_zero_mem, B.Break) )
  in
  let normal_loop_stmt = stmt (S.Loop normal_loop_body_block) in
  let normal_loop_rest =
    B.STreeLoopBreak
      (normal_break_body, (y_zero_mem, normal_loop_stmt, y_zero_mem, B.Normal))
  in
  expect_suspected_gap_invalid "reject_loop_continue_normal_body"
    "S-LoopContinue body control"
    (C.check_stree
       (B.STreeLoopContinue
          ( normal_body,
            normal_loop_rest,
            (y_one_mem, normal_loop_stmt, y_zero_mem, B.Normal) )));
  let fd_returns =
    minimal_main (block [ stmt (S.Return (Some (int_exp 1))) ])
  in
  let body_mem = Memory.enter_function mem0 in
  let body_tree =
    B.BTreeSeq
      ( [ return_const_stree body_mem 1 ],
        (body_mem, fd_returns.S.sbody, body_mem, B.Return (must_value 1)) )
  in
  let out_mem =
    must_ok "leave function" Memory.string_of_error
      (Memory.leave_function body_mem)
  in
  expect_suspected_gap_invalid "reject_function_wrong_return_constructor"
    "F no-return body control"
    (C.check_ftree
       (B.FTreeNoReturn
          (body_tree, (mem0, fd_returns, [], out_mem, B.Return (must_value 1)))));
  let ghost_tree = derive_example (example_path "function_call.c") in
  let ghost_tree =
    match ghost_tree with
    | B.PTreeMainReturn (ftree, (_, mem, value)) ->
        let _, main, _, _, _ = U.f_concl ftree in
        B.PTreeMainReturn (ftree, (file [ S.GFun main ], mem, value))
  in
  expect_suspected_gap_invalid "reject_ghost_callee_function"
    "callee function"
    (C.check_ptree ~use_check_file:false ghost_tree);
  let fd_main = minimal_main (block [ stmt (S.Return (Some (int_exp 0))) ]) in
  let main_input = Memory.enter_function mem0 in
  let main_body_input = Memory.enter_function main_input in
  let main_body =
    B.BTreeSeq
      ( [ return_const_stree main_body_input 0 ],
        ( main_body_input,
          fd_main.S.sbody,
          main_body_input,
          B.Return (must_value 0) ) )
  in
  let main_out =
    must_ok "leave main" Memory.string_of_error
      (Memory.leave_function main_body_input)
  in
  let nonempty_main_input =
    B.PTreeMainReturn
      ( B.FTreeReturn
          (main_body, (main_input, fd_main, [], main_out, B.Return (must_value 0))),
        (file [ S.GFun fd_main ], main_out, must_value 0) )
  in
  expect_suspected_gap_invalid "reject_main_nonempty_input"
    "P-Main input"
    (C.check_ptree ~use_check_file:false nonempty_main_input);
  expect_suspected_gap_invalid "reject_empty_execution_nonempty_block"
    "B-Seq empty execution"
    (C.check_btree
       (B.BTreeSeq
          ([], (mem0, block [ stmt (S.Instr []) ], mem0, B.Normal))));
  let forged_call_tree =
    first_call_assign (derive_example (example_path "function_call.c"))
    |> call_with_forged_callee_signature
  in
  expect_suspected_gap_invalid "reject_call_callee_signature_mismatch"
    "callee signature"
    (C.check_itree forged_call_tree);
  let forged_call_void_tree =
    first_call_assign (derive_example (example_path "function_call.c"))
    |> call_void_with_forged_callee_signature
  in
  expect_suspected_gap_invalid "reject_call_void_callee_signature_mismatch"
    "callee signature"
    (C.check_itree forged_call_void_tree);
  match List.rev !suspected_gap_failures with
  | [] -> ()
  | failures ->
      failwith
        ("suspected gap tests accepted invalid proofs: "
        ^ String.concat "; " failures)

let () =
  List.iter expect_valid_example
    [ example_path "simple.c"; example_path "function_call.c"; example_path "fibonacci.c" ];
  run_expression_errors ();
  run_lvalue_errors ();
  run_instruction_and_call_errors ();
  run_statement_and_block_errors ();
  run_function_and_program_errors ();
  run_suspected_gap_errors ()
