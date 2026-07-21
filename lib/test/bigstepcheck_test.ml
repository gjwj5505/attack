open Language

module S = Syntax
module B = BigStep
module C = BigStepChecker
module U = BigStepUtil

let int_t = Typ.TInt Typ.IInt
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

let var ?(vglob = false) ?(vtemp = false) ?(function_name = "test") name
    typ =
  let vid =
    if vglob then S.VarId.global name
    else S.VarId.local ~function_name name
  in
  { S.vtype = typ; vglob; vtemp; vid }

let function_type return_type formals =
  Typ.TFun
    ( return_type,
      Some
        (List.map
           (fun formal -> (SyntaxUtil.var_name formal, formal.S.vtype))
           formals) )

let function_var name return_type formals =
  var ~vglob:true name (function_type return_type formals)

let stmt skind = { S.labels = []; skind; sid = None }
let block bstmts = { S.bstmts }
let file globals = { S.fileName = "bigstepcheck-test.c"; globals }
let int_exp n = S.Const (S.CInt (Int64.of_int n, Typ.IInt))
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
    match SyntaxChecker.check_file file with
    | Ok () -> ()
    | Error err -> failwith (path ^ ": " ^ SyntaxChecker.string_of_error err)
  end;
  match Derivator.derive_file file with
  | Ok tree -> tree
  | Error err -> failwith (path ^ ": " ^ Derivator.string_of_error err)

let expect_valid_example path =
  let tree = derive_example path in
  expect_valid ("accept_" ^ Filename.basename path)
    (C.check_ptree ~use_check_file:false tree)

let local_binding ?(typ = int_t) ?(value = must_value 1) name =
  let x = var name typ in
  let lval = (S.Var x, S.NoOffset) in
  let loc, mem =
    must_ok "bind local" Memory.string_of_error
      (Memory.bind_local x value (Memory.enter_function Memory.empty))
  in
  (x, lval, loc, mem)

let global_binding ?(value = must_value 1) name =
  let global_var = var ~vglob:true name int_t in
  let obj = Location.Global 0 in
  let loc = { Location.obj; offset = 0 } in
  let info : Memory.object_info = { typ = int_t; size = 1 } in
  let storage : Memory.storage =
    {
      next_object_id = 1;
      objects = Location.ObjectMap.singleton obj info;
      store = Location.LocMap.singleton loc value;
    }
  in
  let global : Memory.global_state =
    {
      bindings = Memory.VarMap.singleton global_var.S.vid loc;
      storage;
    }
  in
  (global_var, loc, { Memory.empty with Memory.global = global })

let memory_with_stack storage locals =
  let stack : Memory.stack_state =
    { frame = { locals }; storage }
  in
  { Memory.empty with Memory.stack = Some stack }

let stack_location id offset =
  { Location.obj = Location.Stack id; offset }

let stack_storage ?(next_object_id = 1)
    ?(objects = Location.ObjectMap.empty)
    ?(store = Location.LocMap.empty) () : Memory.storage =
  { next_object_id; objects; store }

let int_object ?(size = 1) () : Memory.object_info =
  { typ = int_t; size }

let leave_function_mem label caller_mem mem =
  must_ok label Memory.string_of_error
    (Memory.leave_function ~caller_stack:caller_mem.Memory.stack mem)

let valid_ltree () =
  let _, lval, loc, mem = local_binding "x" in
  B.LTreeVar (mem, lval, loc)

let valid_set_itree () =
  let _, lval, loc, mem = local_binding "x" in
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
    S.svar = function_var "main" int_t [];
    sformals = [];
    slocals = [];
    sbody = body;
  }

let ftree_with_fd fd = function
  | B.FTreeReturn (body, (mem, _, args, out_mem, control)) ->
      B.FTreeReturn (body, (mem, fd, args, out_mem, control))
  | B.FTreeNoReturn (body, (mem, _, args, out_mem, control)) ->
      B.FTreeNoReturn (body, (mem, fd, args, out_mem, control))

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

let call_with_mutated_callee_var mutate itree =
  match itree with
  | B.ITreeCallAssign (_, B.CalleeTreeDirect (_, var, _), _, _, _) ->
      call_with_callee_var (mutate var) itree
  | _ -> failwith "expected call assignment tree"

let call_assign_to_void itree =
  match itree with
  | B.ITreeCallAssign
      (_, (B.CalleeTreeDirect (callee_exp, _, _) as callee), args, ftree,
        (mem, _, _)) ->
      let arg_exps =
        List.map (fun arg -> let _, exp, _ = U.e_concl arg in exp) args
      in
      let _, _, _, callee_out, _ = U.f_concl ftree in
      B.ITreeCallVoid
        ( callee,
          args,
          ftree,
          (mem, S.Call (None, callee_exp, arg_exps), callee_out) )
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
      (ltree, B.CalleeTreeDirect (_, callee_var, fd), args, _ftree, concl) ->
      let call_mem, instr, _ = concl in
      let _, _, ret_loc = U.l_concl ltree in
      let arg_values = List.map U.e_value args in
      let forged_var =
        {
          callee_var with
          S.vtype = Typ.TFun (int_t, Some [ ("x", int_t) ]);
        }
      in
      let forged_formal =
        var ~function_name:(SyntaxUtil.var_name fd.S.svar) "renamed" int_t
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
        leave_function_mem "forged leave function" call_mem body_mem
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
      (_, B.CalleeTreeDirect (_, callee_var, fd), args, _ftree, concl) ->
      let call_mem, _, _ = concl in
      let arg_values = List.map U.e_value args in
      let arg_exps = List.map (fun arg -> let _, exp, _ = U.e_concl arg in exp) args in
      let forged_var =
        {
          callee_var with
          S.vtype = Typ.TFun (int_t, Some [ ("x", int_t) ]);
        }
      in
      let forged_formal =
        var ~function_name:(SyntaxUtil.var_name fd.S.svar) "renamed" int_t
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
        leave_function_mem "forged void leave function" call_mem body_mem
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

let run_memory_well_formedness_errors () =
  let check name needle mem =
    expect_invalid name needle
      (C.check_btree
         (B.BTreeSeq ([], (mem, block [], mem, B.Normal))))
  in
  check "reject_memory_negative_next_object_id" "invalid next object id"
    (memory_with_stack (stack_storage ~next_object_id:(-1) ())
       Memory.VarMap.empty);
  let global_obj = Location.Global 0 in
  let wrong_area_objects =
    Location.ObjectMap.singleton global_obj (int_object ())
  in
  check "reject_memory_wrong_object_area" "is not in stack storage"
    (memory_with_stack
       (stack_storage ~objects:wrong_area_objects ())
       Memory.VarMap.empty);
  let invalid_id_obj = Location.Stack 1 in
  let invalid_id_objects =
    Location.ObjectMap.singleton invalid_id_obj (int_object ())
  in
  check "reject_memory_invalid_object_id" "invalid object id"
    (memory_with_stack
       (stack_storage ~next_object_id:1 ~objects:invalid_id_objects ())
       Memory.VarMap.empty);
  let stack_obj = Location.Stack 0 in
  let wrong_size_objects =
    Location.ObjectMap.singleton stack_obj (int_object ~size:2 ())
  in
  check "reject_memory_object_size" "object size mismatch"
    (memory_with_stack
       (stack_storage ~objects:wrong_size_objects ())
       Memory.VarMap.empty);
  let valid_objects =
    Location.ObjectMap.singleton stack_obj (int_object ())
  in
  let stack_loc = stack_location 0 0 in
  let global_id = S.VarId.global "x" in
  check "reject_memory_stack_global_scope" "invalid memory binding scope"
    (memory_with_stack
       (stack_storage ~objects:valid_objects ())
       (Memory.VarMap.singleton global_id stack_loc));
  let local_id = S.VarId.local ~function_name:"f" "x" in
  check "reject_memory_dangling_binding" "invalid memory binding"
    (memory_with_stack (stack_storage ())
       (Memory.VarMap.singleton local_id stack_loc));
  let local_y = S.VarId.local ~function_name:"f" "y" in
  let duplicate_bindings =
    Memory.VarMap.empty
    |> Memory.VarMap.add local_id stack_loc
    |> Memory.VarMap.add local_y stack_loc
  in
  check "reject_memory_duplicate_binding_location"
    "duplicate memory binding location"
    (memory_with_stack
       (stack_storage ~objects:valid_objects ())
       duplicate_bindings);
  let out_of_bounds_loc = stack_location 0 1 in
  let out_of_bounds_store =
    Location.LocMap.singleton out_of_bounds_loc (must_value 1)
  in
  check "reject_memory_stored_location" "invalid stored location"
    (memory_with_stack
       (stack_storage ~objects:valid_objects ~store:out_of_bounds_store ())
       Memory.VarMap.empty);
  let pointer_store =
    Location.LocMap.singleton stack_loc (Value.ptr bad_loc)
  in
  check "reject_memory_stored_value_type" "stored value type mismatch"
    (memory_with_stack
       (stack_storage ~objects:valid_objects ~store:pointer_store ())
       Memory.VarMap.empty);
  let pointer_info : Memory.object_info =
    { typ = Typ.TPtr int_t; size = 1 }
  in
  let pointer_objects =
    Location.ObjectMap.singleton stack_obj pointer_info
  in
  check "reject_memory_unsupported_object_type" "unsupported object type"
    (memory_with_stack
       (stack_storage ~objects:pointer_objects ())
       Memory.VarMap.empty)

let break_btree mem =
  let break_stmt = stmt S.Break in
  B.BTreeSeq
    ([ B.STreeBreak (mem, break_stmt, mem, B.Break) ],
     (mem, block [ break_stmt ], mem, B.Break))

let run_expression_errors () =
  expect_invalid "reject_const_value" "E-Const value"
    (C.check_etree (B.ETreeConst (mem0, int_exp 1, must_value 2)));
  let x, lval, _, _ = local_binding "x" in
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
          )))

let run_lvalue_errors () =
  let x = var "x" int_t in
  expect_invalid "reject_ltree_var_unbound" "L-Var failed"
    (C.check_ltree (B.LTreeVar (mem0, (S.Var x, S.NoOffset), bad_loc)));
  let _, lval, _, mem = local_binding "x" in
  expect_invalid "reject_ltree_var_location" "L-Var location"
    (C.check_ltree (B.LTreeVar (mem, lval, bad_loc)))

let run_instruction_and_call_errors () =
  let set_tree = valid_set_itree () in
  begin
    match set_tree with
    | B.ITreeSet (ltree, _, (mem, S.Set (lval, _), out_mem)) ->
        let int_etree = B.ETreeConst (mem, int_exp 2, must_value 2) in
        expect_invalid "reject_set_subject" "I-Set subject"
          (C.check_itree
             (B.ITreeSet
                (ltree, int_etree, (mem, S.Set (lval, int_exp 9), out_mem))));
        expect_invalid "reject_set_output" "I-Set output"
          (C.check_itree
             (B.ITreeSet
                (ltree, int_etree, (mem, S.Set (lval, int_exp 2), mem))))
    | _ -> failwith "expected set tree"
  end;
  let call_tree = first_call_assign (derive_example (example_path "function_call.c")) in
  expect_valid "accept_call_void_discard_return"
    (C.check_itree (call_assign_to_void call_tree));
  let callee typ = var ~vglob:true "f" typ in
  let one_param = Some [ ("x", int_t) ] in
  expect_invalid "reject_call_callee_varinfo_mismatch" "Callee direct: var/function mismatch"
    (C.check_itree
       (call_with_callee_var
          (var ~vglob:true "g" (Typ.TFun (int_t, one_param)))
          call_tree));
  expect_invalid "reject_call_callee_vglob_mismatch"
    "Callee direct: var/function mismatch"
    (C.check_itree
       (call_with_mutated_callee_var
          (fun var -> { var with S.vglob = false })
          call_tree));
  expect_invalid "reject_call_callee_vtemp_mismatch"
    "Callee direct: var/function mismatch"
    (C.check_itree
       (call_with_mutated_callee_var
          (fun var -> { var with S.vtemp = true })
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
  expect_invalid "reject_call_assigning_void" "assigning void call result"
    (C.check_itree
       (call_with_callee_var (callee (Typ.TFun (void_t, one_param))) call_tree));
  expect_invalid "reject_call_formal_name_mismatch" "callee signature mismatch"
    (C.check_itree
       (call_with_callee_var
          (callee (Typ.TFun (int_t, Some [ ("renamed", int_t) ])))
          call_tree));
  expect_invalid "reject_call_arg_input" "I-CallAssign argument input"
    (C.check_itree (call_with_first_arg_mem (Memory.enter_function mem0) call_tree))

let run_statement_and_block_errors () =
  expect_valid "accept_return_none_void"
    (C.check_stree ~return_type:void_t
       (B.STreeReturnNone
          (mem0, stmt (S.Return None), mem0, B.ReturnVoid)));
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
  let empty_block = block [] in
  let empty_body = empty_btree mem0 in
  let block_stmt = stmt (S.Block empty_block) in
  let valid_block_tree =
    B.STreeBlock
      (empty_body, (mem0, block_stmt, mem0, B.Normal))
  in
  expect_valid "accept_block" (C.check_stree valid_block_tree);
  expect_invalid "reject_block_output" "S-Block output"
    (C.check_stree
       (B.STreeBlock
          ( empty_body,
            (mem0, block_stmt, Memory.enter_function mem0, B.Normal) )));
  expect_invalid "reject_block_control" "S-Block control"
    (C.check_stree
       (B.STreeBlock
          (empty_body, (mem0, block_stmt, mem0, B.Break))));
  let loop_return_stmt = stmt (S.Return (Some (int_exp 1))) in
  let loop_return_block = block [ loop_return_stmt ] in
  let loop_return_body =
    B.BTreeSeq
      ( [ return_const_stree mem0 1 ],
        (mem0, loop_return_block, mem0, B.Return (must_value 1)) )
  in
  let loop_stmt = stmt (S.Loop loop_return_block) in
  expect_valid "accept_loop_return"
    (C.check_stree ~return_type:int_t
       (B.STreeLoopReturn
          ( loop_return_body,
            (mem0, loop_stmt, mem0, B.Return (must_value 1)) )));
  let normal_loop_stmt = stmt (S.Loop empty_block) in
  expect_invalid "reject_loop_return_normal_body" "body did not return"
    (C.check_stree ~return_type:int_t
       (B.STreeLoopReturn
          (empty_body, (mem0, normal_loop_stmt, mem0, B.Normal))));
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

let run_function_top_frame_tests () =
  let formal = var ~function_name:"arg_callee" "arg" int_t in
  let arg_fd =
    {
      S.svar = function_var "arg_callee" void_t [ formal ];
      sformals = [ formal ];
      slocals = [];
      sbody = block [];
    }
  in
  let arg_value = must_value 1 in
  let arg_ftree bound_value =
    let body_mem =
      must_ok "bind callee argument" Memory.string_of_error
        (Memory.bind_local formal bound_value (Memory.enter_function mem0))
      |> snd
    in
    let body = empty_btree body_mem in
    let out_mem = leave_function_mem "leave argument callee" mem0 body_mem in
    B.FTreeNoReturn
      (body, (mem0, arg_fd, [ arg_value ], out_mem, B.ReturnVoid))
  in
  expect_valid "accept_function_argument_binding"
    (C.check_ftree (arg_ftree arg_value));
  expect_invalid "reject_function_argument_binding" "F body input"
    (C.check_ftree (arg_ftree (must_value 2)));
  let wrong_arity_ftree =
    match arg_ftree arg_value with
    | B.FTreeNoReturn (body, (mem, fd, _, out_mem, control)) ->
        B.FTreeNoReturn (body, (mem, fd, [], out_mem, control))
    | B.FTreeReturn _ -> failwith "expected no-return function tree"
  in
  expect_invalid "reject_function_argument_arity" "F arguments: arity mismatch"
    (C.check_ftree wrong_arity_ftree);
  let pointer_argument_ftree =
    match arg_ftree arg_value with
    | B.FTreeNoReturn (body, (mem, fd, _, out_mem, control)) ->
        B.FTreeNoReturn
          (body, (mem, fd, [ Value.ptr bad_loc ], out_mem, control))
    | B.FTreeReturn _ -> failwith "expected no-return function tree"
  in
  expect_invalid "reject_function_pointer_argument" "expected int value"
    (C.check_ftree pointer_argument_ftree);
  let expect_invalid_metadata name needle invalid_fd =
    expect_invalid name needle
      (C.check_ftree
         (ftree_with_fd invalid_fd (arg_ftree arg_value)))
  in
  let wrong_svar_scope =
    {
      arg_fd with
      S.svar =
        {
          arg_fd.S.svar with
          S.vid =
            S.VarId.local ~function_name:"arg_callee" "arg_callee";
        };
    }
  in
  expect_invalid_metadata "reject_function_svar_scope"
    "function svar must have global scope" wrong_svar_scope;
  let nonglobal_svar =
    { arg_fd with S.svar = { arg_fd.S.svar with S.vglob = false } }
  in
  expect_invalid_metadata "reject_function_svar_vglob"
    "function svar must be global" nonglobal_svar;
  let temporary_svar =
    { arg_fd with S.svar = { arg_fd.S.svar with S.vtemp = true } }
  in
  expect_invalid_metadata "reject_function_svar_vtemp"
    "function svar cannot be temporary" temporary_svar;
  let wrong_scope_formal =
    {
      formal with
      S.vid = S.VarId.local ~function_name:"other" "arg";
    }
  in
  expect_invalid_metadata "reject_function_formal_scope" "invalid local scope"
    { arg_fd with S.sformals = [ wrong_scope_formal ] };
  let global_formal = { formal with S.vglob = true } in
  expect_invalid_metadata "reject_function_formal_vglob" "local marked global"
    { arg_fd with S.sformals = [ global_formal ] };
  let nonint_formal = { formal with S.vtype = Typ.TVoid } in
  let nonint_formal_svar =
    {
      arg_fd.S.svar with
      S.vtype = Typ.TFun (void_t, Some [ ("arg", Typ.TVoid) ]);
    }
  in
  expect_invalid_metadata "reject_function_formal_nonint"
    "outside the int-only subset"
    {
      arg_fd with
      S.svar = nonint_formal_svar;
      sformals = [ nonint_formal ];
    };
  let duplicate_local = { formal with S.vtemp = true } in
  expect_invalid_metadata "reject_function_duplicate_formal_local"
    "duplicate formal/local name"
    { arg_fd with S.slocals = [ duplicate_local ] };
  let mismatched_occurrence = { formal with S.vtemp = true } in
  let mismatched_lval = (S.Var mismatched_occurrence, S.NoOffset) in
  let mismatched_instr = S.Set (mismatched_lval, int_exp 0) in
  expect_invalid_metadata "reject_function_body_local_metadata"
    "local declaration mismatch"
    {
      arg_fd with
      S.sbody = block [ stmt (S.Instr [ mismatched_instr ]) ];
    };
  let other_local = var ~function_name:"other" "arg" int_t in
  let other_lval = (S.Var other_local, S.NoOffset) in
  let other_instr = S.Set (other_lval, int_exp 0) in
  expect_invalid_metadata "reject_function_body_other_scope"
    "reference to another function local"
    {
      arg_fd with
      S.sbody = block [ stmt (S.Instr [ other_instr ]) ];
    };
  let expect_invalid_signature name vtype =
    let invalid_fd =
      { arg_fd with S.svar = { arg_fd.S.svar with S.vtype } }
    in
    expect_invalid name "F: function signature mismatch"
      (C.check_ftree (ftree_with_fd invalid_fd (arg_ftree arg_value)))
  in
  expect_invalid_signature "reject_function_nonfunction_type" int_t;
  expect_invalid_signature "reject_function_without_parameter_types"
    (Typ.TFun (void_t, None));
  expect_invalid_signature "reject_function_formal_name_mismatch"
    (Typ.TFun (void_t, Some [ ("renamed", int_t) ]));
  expect_invalid_signature "reject_function_too_few_formals"
    (Typ.TFun (void_t, Some []));
  expect_invalid_signature "reject_function_too_many_formals"
    (Typ.TFun
       (void_t, Some [ ("arg", int_t); ("extra", int_t) ]));
  let value_returning_fd =
    {
      arg_fd with
      S.svar = function_var "arg_callee" int_t [ formal ];
    }
  in
  expect_invalid "reject_nonvoid_function_without_return_value"
    "F no-return type"
    (C.check_ftree
       (ftree_with_fd value_returning_fd (arg_ftree arg_value)));
  let _, _, caller_loc, caller_mem =
    local_binding ~value:(must_value 7) "caller_x"
  in
  let return_fd =
    {
      S.svar = function_var "return_callee" void_t [];
      sformals = [];
      slocals = [];
      sbody = block [];
    }
  in
  let body_mem = Memory.enter_function caller_mem in
  let body = empty_btree body_mem in
  let out_mem = leave_function_mem "leave return callee" caller_mem body_mem in
  let ftree out_mem =
    B.FTreeNoReturn
      (body, (caller_mem, return_fd, [], out_mem, B.ReturnVoid))
  in
  expect_valid "accept_function_restores_caller_stack"
    (C.check_ftree (ftree out_mem));
  let changed_caller_mem =
    must_ok "change caller after return" Memory.string_of_error
      (Memory.write caller_loc (must_value 8) caller_mem)
  in
  expect_invalid "reject_function_changed_caller_stack" "F output"
    (C.check_ftree (ftree changed_caller_mem));
  let outer_var = var ~function_name:"outer" "outer_x" int_t in
  let _, outer_mem =
    must_ok "bind outer local" Memory.string_of_error
      (Memory.bind_local outer_var (must_value 7)
         (Memory.enter_function Memory.empty))
  in
  let middle_formal = var ~function_name:"middle" "middle_arg" int_t in
  let inner_fd =
    {
      S.svar = function_var "inner" void_t [];
      sformals = [];
      slocals = [];
      sbody = block [];
    }
  in
  let middle_body_mem =
    must_ok "bind middle formal" Memory.string_of_error
      (Memory.bind_local middle_formal (must_value 5)
         (Memory.enter_function outer_mem))
    |> snd
  in
  let middle_loc =
    must_ok "middle formal location" Memory.string_of_error
      (Memory.loc_of_var middle_formal middle_body_mem)
  in
  let inner_body_mem = Memory.enter_function middle_body_mem in
  let inner_body = empty_btree inner_body_mem in
  let inner_out =
    leave_function_mem "leave inner" middle_body_mem inner_body_mem
  in
  let inner_ftree out_mem =
    B.FTreeNoReturn
      (inner_body, (middle_body_mem, inner_fd, [], out_mem, B.ReturnVoid))
  in
  let inner_callee_exp =
    S.Lval (S.Var inner_fd.S.svar, S.NoOffset)
  in
  let inner_callee =
    B.CalleeTreeDirect (inner_callee_exp, inner_fd.S.svar, inner_fd)
  in
  let inner_call_instr = S.Call (None, inner_callee_exp, []) in
  let middle_fd =
    {
      S.svar = function_var "middle" void_t [ middle_formal ];
      sformals = [ middle_formal ];
      slocals = [];
      sbody = block [ stmt (S.Instr [ inner_call_instr ]) ];
    }
  in
  let nested_middle_ftree inner_ftree inner_call_out =
    let call_tree =
      B.ITreeCallVoid
        ( inner_callee,
          [],
          inner_ftree,
          (middle_body_mem, inner_call_instr, inner_call_out) )
    in
    let call_stmt =
      B.STreeInstr
        ( [ call_tree ],
          ( middle_body_mem,
            stmt (S.Instr [ inner_call_instr ]),
            inner_call_out,
            B.Normal ) )
    in
    let middle_body =
      B.BTreeSeq
        ( [ call_stmt ],
          ( middle_body_mem,
            middle_fd.S.sbody,
            inner_call_out,
            B.Normal ) )
    in
    let middle_out =
      leave_function_mem "leave middle" outer_mem inner_call_out
    in
    B.FTreeNoReturn
      ( middle_body,
        (outer_mem, middle_fd, [ must_value 5 ], middle_out, B.ReturnVoid) )
  in
  expect_valid "accept_nested_call_restores_intermediate_stack"
    (C.check_ftree
       (nested_middle_ftree (inner_ftree inner_out) inner_out));
  let changed_middle_mem =
    must_ok "change middle caller" Memory.string_of_error
      (Memory.write middle_loc (must_value 6) inner_out)
  in
  expect_invalid "reject_nested_call_changes_intermediate_stack" "F output"
    (C.check_ftree
       (nested_middle_ftree
          (inner_ftree changed_middle_mem)
          changed_middle_mem));
  let callee_local = var ~function_name:"local_callee" "tmp" int_t in
  let local_fd =
    {
      S.svar = function_var "local_callee" void_t [];
      sformals = [];
      slocals = [ callee_local ];
      sbody = block [];
    }
  in
  let local_body_mem =
    must_ok "allocate callee local" Memory.string_of_error
      (Memory.allocate_local callee_local (Memory.enter_function caller_mem))
    |> snd
  in
  let local_body = empty_btree local_body_mem in
  let local_out =
    leave_function_mem "leave local callee" caller_mem local_body_mem
  in
  let local_ftree out_mem =
    B.FTreeNoReturn
      (local_body, (caller_mem, local_fd, [], out_mem, B.ReturnVoid))
  in
  expect_valid "accept_function_discards_callee_local_storage"
    (C.check_ftree (local_ftree local_out));
  expect_invalid "reject_function_leaks_callee_local_storage" "F output"
    (C.check_ftree (local_ftree local_body_mem));
  let global_var, global_loc, global_mem = global_binding "g" in
  let global_caller = var ~function_name:"caller" "caller_x" int_t in
  let global_caller_loc, global_caller_mem =
    must_ok "bind global-test caller" Memory.string_of_error
      (Memory.bind_local global_caller (must_value 7)
         (Memory.enter_function global_mem))
  in
  let global_body_mem = Memory.enter_function global_caller_mem in
  let global_lval = (S.Var global_var, S.NoOffset) in
  let global_exp = int_exp 2 in
  let global_instr = S.Set (global_lval, global_exp) in
  let global_ltree = B.LTreeVar (global_body_mem, global_lval, global_loc) in
  let global_etree = B.ETreeConst (global_body_mem, global_exp, must_value 2) in
  let changed_global_body_mem =
    must_ok "write callee global" Memory.string_of_error
      (Memory.write global_loc (must_value 2) global_body_mem)
  in
  let global_itree =
    B.ITreeSet
      (global_ltree, global_etree,
       (global_body_mem, global_instr, changed_global_body_mem))
  in
  let global_stmt =
    B.STreeInstr
      ( [ global_itree ],
        ( global_body_mem,
          stmt (S.Instr [ global_instr ]),
          changed_global_body_mem,
          B.Normal ) )
  in
  let global_fd =
    {
      S.svar = function_var "global_callee" void_t [];
      sformals = [];
      slocals = [];
      sbody = block [ stmt (S.Instr [ global_instr ]) ];
    }
  in
  let global_body =
    B.BTreeSeq
      ( [ global_stmt ],
        ( global_body_mem,
          global_fd.S.sbody,
          changed_global_body_mem,
          B.Normal ) )
  in
  let global_out =
    leave_function_mem "leave global callee" global_caller_mem
      changed_global_body_mem
  in
  let global_ftree out_mem =
    B.FTreeNoReturn
      (global_body, (global_caller_mem, global_fd, [], out_mem, B.ReturnVoid))
  in
  expect_valid "accept_function_preserves_global_update_and_caller_stack"
    (C.check_ftree (global_ftree global_out));
  let caller_value =
    must_ok "read restored caller" Memory.string_of_error
      (Memory.read global_caller_loc global_out)
  in
  let global_value =
    must_ok "read updated global" Memory.string_of_error
      (Memory.read global_loc global_out)
  in
  if caller_value <> must_value 7 || global_value <> must_value 2 then
    failwith "global/caller state was not preserved across function return";
  let lost_global_out =
    { global_out with Memory.global = global_caller_mem.Memory.global }
  in
  expect_invalid "reject_function_loses_global_update" "F output"
    (C.check_ftree (global_ftree lost_global_out))

let run_function_and_program_errors () =
  let valid = derive_example (example_path "simple.c") in
  let bad_output =
    mutate_main_ftree
      (function
        | B.FTreeReturn (btree, (mem, fd, args, _, control)) ->
            B.FTreeReturn
              (btree, (mem, fd, args, Memory.enter_function mem0, control))
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
    let fd = minimal_main (block []) in
    let ghost = var ~function_name:"main" "ghost" int_t in
    let body_mem =
      must_ok "bind forged body local" Memory.string_of_error
        (Memory.bind_local ghost (must_value 1) (Memory.enter_function mem0))
      |> snd
    in
    let btree = empty_btree body_mem in
    let out_mem = leave_function_mem "leave forged body" mem0 body_mem in
    B.FTreeNoReturn
      (btree, (mem0, fd, [], out_mem, B.ReturnVoid))
  in
  expect_invalid "reject_function_body_input" "F body input"
    (C.check_ftree bad_body_input);
  let bad_p_output =
    mutate_main_concl
      (fun (file, _, value) ->
        (file, Memory.enter_function mem0, value))
      valid
  in
  expect_invalid "reject_program_output" "P-Main output"
    (C.check_ptree ~use_check_file:false bad_p_output);
  let bad_p_value =
    mutate_main_concl (fun (file, mem, _) -> (file, mem, must_value 99)) valid
  in
  expect_invalid "reject_program_value" "P-Main value"
    (C.check_ptree ~use_check_file:false bad_p_value);
  let bad_pointer_value =
    mutate_main_concl
      (fun (file, mem, _) -> (file, mem, Value.ptr bad_loc))
      valid
  in
  expect_invalid "reject_program_pointer_value" "P value: expected int value"
    (C.check_ptree ~use_check_file:false bad_pointer_value);
  let no_main_file = file [] in
  let bad_file = mutate_main_concl (fun (_, mem, value) -> (no_main_file, mem, value)) valid in
  expect_invalid "reject_program_file" "missing main function" (C.check_ptree bad_file);
  let other_main = minimal_main (block [ stmt (S.Return (Some (int_exp 0))) ]) in
  let mismatch_file =
    file [ S.GFun { other_main with S.svar = var ~vglob:true "main" int_t } ]
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
    let out_mem = leave_function_mem "leave function" mem0 body_mem in
    B.PTreeMainReturn
      (B.FTreeNoReturn (btree, (mem0, fd, [], out_mem, B.Normal)),
       (file [ S.GFun fd ], out_mem, must_value 0))
  in
  expect_invalid "reject_program_no_return" "F no-return type"
    (C.check_tree (B.PTree no_return))

let run_regression_errors () =
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
  let x, x_lval, x_loc, x_one_mem = local_binding "x" in
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
  expect_invalid "reject_loop_repeat_continue_body"
    "S-LoopRepeat body control"
    (C.check_stree
       (B.STreeLoopRepeat
          ( continue_body,
            continue_loop_rest,
            (x_one_mem, continue_loop_stmt, x_zero_mem, B.Normal) )));
  let y, y_lval, y_loc, y_one_mem = local_binding "y" in
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
  expect_invalid "reject_loop_continue_normal_body"
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
    leave_function_mem "leave function" mem0 body_mem
  in
  expect_invalid "reject_function_wrong_return_constructor"
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
  expect_invalid "reject_ghost_callee_function"
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
    leave_function_mem "leave main" main_input main_body_input
  in
  let nonempty_main_input =
    B.PTreeMainReturn
      ( B.FTreeReturn
          (main_body, (main_input, fd_main, [], main_out, B.Return (must_value 0))),
        (file [ S.GFun fd_main ], main_out, must_value 0) )
  in
  expect_invalid "reject_main_nonempty_input"
    "P-Main input"
    (C.check_ptree ~use_check_file:false nonempty_main_input);
  expect_invalid "reject_empty_execution_nonempty_block"
    "B-Seq empty execution"
    (C.check_btree
       (B.BTreeSeq
          ([], (mem0, block [ stmt (S.Instr []) ], mem0, B.Normal))));
  let forged_call_tree =
    first_call_assign (derive_example (example_path "function_call.c"))
    |> call_with_forged_callee_signature
  in
  expect_invalid "reject_call_callee_signature_mismatch"
    "function signature"
    (C.check_itree forged_call_tree);
  let forged_call_void_tree =
    first_call_assign (derive_example (example_path "function_call.c"))
    |> call_void_with_forged_callee_signature
  in
  expect_invalid "reject_call_void_callee_signature_mismatch"
    "function signature"
    (C.check_itree forged_call_void_tree)

let () =
  List.iter expect_valid_example
    [ example_path "simple.c"; example_path "function_call.c"; example_path "fibonacci.c" ];
  run_memory_well_formedness_errors ();
  run_expression_errors ();
  run_lvalue_errors ();
  run_instruction_and_call_errors ();
  run_statement_and_block_errors ();
  run_function_top_frame_tests ();
  run_function_and_program_errors ();
  run_regression_errors ()
