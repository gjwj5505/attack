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
    (C.check_ptree ~check_file:false tree)

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
       (call_with_callee_var (callee (Typ.TFun (void_t, one_param))) call_tree))

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
    (C.check_ptree ~check_file:false bad_output);
  let bad_control =
    mutate_main_ftree
      (function
        | B.FTreeReturn (btree, (mem, fd, args, out_mem, _)) ->
            B.FTreeReturn (btree, (mem, fd, args, out_mem, B.Normal))
        | tree -> tree)
      valid
  in
  expect_invalid "reject_function_control" "F control"
    (C.check_ptree ~check_file:false bad_control);
  let bad_p_output =
    mutate_main_concl (fun (file, _, value) -> (file, mem0, value)) valid
  in
  expect_invalid "reject_program_output" "P-Main output"
    (C.check_ptree ~check_file:false bad_p_output);
  let bad_p_value =
    mutate_main_concl (fun (file, mem, _) -> (file, mem, must_value 99)) valid
  in
  expect_invalid "reject_program_value" "P-Main value"
    (C.check_ptree ~check_file:false bad_p_value);
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
    (C.check_ptree ~check_file:false bad_main);
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
  expect_invalid "reject_program_no_return" "did not return"
    (C.check_tree (B.PTree no_return))

let () =
  List.iter expect_valid_example
    [ example_path "simple.c"; example_path "function_call.c"; example_path "fibonacci.c" ];
  run_expression_errors ();
  run_lvalue_errors ();
  run_instruction_and_call_errors ();
  run_statement_and_block_errors ();
  run_function_and_program_errors ()
