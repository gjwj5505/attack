module S = Language.Syntax
module SyntaxChecker = Language.SyntaxChecker

let int_t = Language.Typ.TInt Language.Typ.IInt
let void_t = Language.Typ.TVoid

let global_var ?(vtemp = false) name typ =
  { S.vtype = typ; vglob = true; vtemp; vid = S.VarId.global name }

let local_var ?(vtemp = false) ~function_name name typ =
  {
    S.vtype = typ;
    vglob = false;
    vtemp;
    vid = S.VarId.local ~function_name name;
  }

let stmt skind = { S.labels = []; skind; sid = None }
let block bstmts = { S.bstmts }

let int_const n = S.Exp.Const (S.Exp.CInt (Int64.of_int n, Language.Typ.IInt))
let var_exp var = S.Exp.Lval (S.Var var, S.NoOffset)

let function_type return_type formals =
  Language.Typ.TFun
    ( return_type,
      Some
        (List.map
           (fun formal -> (Language.SyntaxUtil.var_name formal, formal.S.vtype))
           formals) )

let function_var name return_type formals =
  global_var name (function_type return_type formals)

let int_fun ?(formals = []) ?(locals = []) name body =
  {
    S.svar = function_var name int_t formals;
    sformals = formals;
    slocals = locals;
    sbody = block body;
  }

let main_fun ?(ret = int_t) ?(formals = []) ?(locals = []) body =
  {
    S.svar = function_var "main" ret formals;
    sformals = formals;
    slocals = locals;
    sbody = block body;
  }

let file globals = { S.fileName = "check-test.c"; globals }

let accept_minimal_main =
  (* Expected: Ok. Valid int main(void) returning 0. *)
  file [ S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]) ]

let reject_missing_main =
  (* Expected: Error Missing_main. No GFun named main exists. *)
  file []

let reject_multiple_main =
  (* Expected: Error Multiple_main. Two function definitions named main exist. *)
  file
    [
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
      S.GFun
        {
          S.svar = function_var "main" int_t [];
          sformals = [];
          slocals = [];
          sbody = block [ stmt (S.Return (Some (int_const 0))) ];
        };
    ]

let reject_invalid_main_type =
  (* Expected: Error (Invalid_main_type TVoid). main must return int. *)
  file [ S.GFun (main_fun ~ret:void_t [ stmt (S.Return None) ]) ]

let reject_main_with_parameters =
  (* Expected: Error Main_with_parameters. main must be int main(void). *)
  let argc = local_var ~function_name:"main" "argc" int_t in
  file
    [
      S.GFun
        (main_fun ~formals:[ argc ] [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let reject_duplicate_global_name =
  (* Expected: Error (Duplicate_global_name "g"). *)
  let g1 = global_var "g" int_t in
  let g2 = global_var "g" int_t in
  file
    [
      S.GVarDecl g1;
      S.GVarDecl g2;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let reject_duplicate_formal_name =
  (* Expected: Error duplicate local name in f: x. *)
  let x1 = local_var ~function_name:"f" "x" int_t in
  let x2 = local_var ~function_name:"f" "x" int_t in
  let f =
    {
      S.svar = function_var "f" int_t [ x1; x2 ];
      sformals = [ x1; x2 ];
      slocals = [];
      sbody = block [ stmt (S.Return (Some (int_const 0))) ];
    }
  in
  file
    [
      S.GFun f;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let reject_duplicate_local_name =
  (* Expected: Error duplicate local name in f: x. *)
  let x1 = local_var ~function_name:"f" "x" int_t in
  let x2 = local_var ~function_name:"f" "x" int_t in
  let f =
    {
      S.svar = function_var "f" int_t [];
      sformals = [];
      slocals = [ x1; x2 ];
      sbody = block [ stmt (S.Return (Some (int_const 0))) ];
    }
  in
  file
    [
      S.GFun f;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let reject_formal_local_name_collision =
  (* Expected: Error duplicate local name in f: x. *)
  let formal = local_var ~function_name:"f" "x" int_t in
  let local = local_var ~function_name:"f" "x" int_t in
  let f =
    {
      S.svar = function_var "f" int_t [ formal ];
      sformals = [ formal ];
      slocals = [ local ];
      sbody = block [ stmt (S.Return (Some (int_const 0))) ];
    }
  in
  file
    [
      S.GFun f;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let reject_break_outside_loop =
  (* Expected: Error Break_outside_loop. This AST cannot come from valid C
     source, but the synthesizer can construct it directly. *)
  file [ S.GFun (main_fun [ stmt S.Break; stmt (S.Return (Some (int_const 0))) ]) ]

let reject_continue_outside_loop =
  (* Expected: Error Continue_outside_loop. This AST cannot come from valid C
     source, but the synthesizer can construct it directly. *)
  file
    [ S.GFun (main_fun [ stmt S.Continue; stmt (S.Return (Some (int_const 0))) ]) ]

let reject_return_value_in_void_function =
  (* Expected: Error Return_value_in_void_function. Return expression presence
     must match the enclosing function return type. *)
  let f =
    {
      S.svar = function_var "f" void_t [];
      sformals = [];
      slocals = [];
      sbody = block [ stmt (S.Return (Some (int_const 1))) ];
    }
  in
  file
    [
      S.GFun f;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let reject_return_without_value_in_nonvoid_function =
  (* Expected: Error (Return_without_value_in_nonvoid_function int). Return
     expression presence must match the enclosing function return type. *)
  let f =
    {
      S.svar = function_var "f" int_t [];
      sformals = [];
      slocals = [];
      sbody = block [ stmt (S.Return None) ];
    }
  in
  file
    [
      S.GFun f;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let accept_break_continue_inside_loop =
  (* Expected: Ok. Break and continue are valid inside Loop. *)
  file
    [
      S.GFun
        (main_fun
           [
             stmt (S.Loop (block [ stmt S.Continue; stmt S.Break ]));
             stmt (S.Return (Some (int_const 0)));
           ]);
    ]

let invalid_global_scope_var =
  {
    (global_var "g" int_t) with
    S.vid = S.VarId.local ~function_name:"f" "g";
  }

let reject_invalid_global_scope =
  file
    [
      S.GVarDecl invalid_global_scope_var;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let invalid_function_scope_var =
  {
    (function_var "f" int_t []) with
    S.vid = S.VarId.local ~function_name:"f" "f";
  }

let reject_invalid_function_scope =
  let f =
    {
      S.svar = invalid_function_scope_var;
      sformals = [];
      slocals = [];
      sbody = block [ stmt (S.Return (Some (int_const 0))) ];
    }
  in
  file
    [
      S.GFun f;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let invalid_formal_scope_var =
  local_var ~function_name:"g" "x" int_t

let reject_invalid_formal_scope =
  let f =
    int_fun ~formals:[ invalid_formal_scope_var ] "f"
      [ stmt (S.Return (Some (int_const 0))) ]
  in
  file
    [
      S.GFun f;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let invalid_local_scope_var =
  local_var ~function_name:"g" "x" int_t

let reject_invalid_local_scope =
  let f =
    int_fun ~locals:[ invalid_local_scope_var ] "f"
      [ stmt (S.Return (Some (int_const 0))) ]
  in
  file
    [
      S.GFun f;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let cross_function_reference =
  local_var ~function_name:"g" "x" int_t

let reject_cross_function_reference =
  let f_x = local_var ~function_name:"f" "x" int_t in
  let g_x = local_var ~function_name:"g" "x" int_t in
  let f =
    int_fun ~locals:[ f_x ] "f"
      [ stmt (S.Return (Some (var_exp cross_function_reference))) ]
  in
  let g =
    int_fun ~locals:[ g_x ] "g"
      [ stmt (S.Return (Some (var_exp g_x))) ]
  in
  file
    [
      S.GFun f;
      S.GFun g;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let mismatched_temp_declaration =
  local_var ~function_name:"f" "x" int_t

let mismatched_temp_occurrence =
  { mismatched_temp_declaration with S.vtemp = true }

let reject_variable_temp_mismatch =
  let f =
    int_fun ~locals:[ mismatched_temp_declaration ] "f"
      [ stmt (S.Return (Some (var_exp mismatched_temp_occurrence))) ]
  in
  file
    [
      S.GFun f;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let undeclared_global_reference = global_var "missing" int_t

let reject_undeclared_global_reference =
  file
    [
      S.GFun
        (main_fun
           [ stmt (S.Return (Some (var_exp undeclared_global_reference))) ]);
    ]

let initializer_local_reference =
  local_var ~function_name:"main" "x" int_t

let reject_local_reference_in_global_initializer =
  let g = global_var "g" int_t in
  file
    [
      S.GVar
        (g, { init = Some (S.SingleInit (var_exp initializer_local_reference)) });
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let accept_same_local_name_in_different_functions =
  let f_x = local_var ~function_name:"f" "x" int_t in
  let g_x = local_var ~function_name:"g" "x" int_t in
  let f =
    int_fun ~locals:[ f_x ] "f"
      [ stmt (S.Return (Some (var_exp f_x))) ]
  in
  let g =
    int_fun ~locals:[ g_x ] "g"
      [ stmt (S.Return (Some (var_exp g_x))) ]
  in
  file
    [
      S.GFun f;
      S.GFun g;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let reject_global_and_local_same_name =
  let global_x = global_var "x" int_t in
  let local_x = local_var ~function_name:"main" "x" int_t in
  file
    [
      S.GVar
        (global_x, { init = Some (S.SingleInit (int_const 1)) });
      S.GFun
        (main_fun ~locals:[ local_x ]
           [ stmt (S.Return (Some (var_exp local_x))) ]);
    ]

let accept_global_reference =
  let g = global_var "g" int_t in
  file
    [
      S.GVar (g, { init = Some (S.SingleInit (int_const 1)) });
      S.GFun (main_fun [ stmt (S.Return (Some (var_exp g))) ]);
    ]

let invalid_function_type_var = global_var "f" int_t

let reject_invalid_function_type =
  let f =
    {
      S.svar = invalid_function_type_var;
      sformals = [];
      slocals = [];
      sbody = block [ stmt (S.Return (Some (int_const 0))) ];
    }
  in
  file
    [
      S.GFun f;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let incomplete_function_variable =
  global_var "f" (Language.Typ.TFun (int_t, None))

let reject_incomplete_function_type =
  let f =
    {
      S.svar = incomplete_function_variable;
      sformals = [];
      slocals = [];
      sbody = block [ stmt (S.Return (Some (int_const 0))) ];
    }
  in
  file
    [
      S.GFun f;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let accept_multi_formal_function_signature =
  let x = local_var ~function_name:"f" "x" int_t in
  let y = local_var ~function_name:"f" "y" int_t in
  let f =
    int_fun ~formals:[ x; y ] "f"
      [ stmt (S.Return (Some (var_exp x))) ]
  in
  file
    [
      S.GFun f;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let name_mismatch_formal = local_var ~function_name:"f" "x" int_t

let name_mismatch_function_variable =
  global_var "f" (Language.Typ.TFun (int_t, Some [ ("y", int_t) ]))

let reject_function_formal_name_mismatch =
  let f =
    {
      S.svar = name_mismatch_function_variable;
      sformals = [ name_mismatch_formal ];
      slocals = [];
      sbody = block [ stmt (S.Return (Some (int_const 0))) ];
    }
  in
  file
    [
      S.GFun f;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let count_mismatch_formal = local_var ~function_name:"f" "x" int_t

let too_few_formals_function_variable =
  global_var "f" (Language.Typ.TFun (int_t, Some []))

let reject_function_too_few_formals =
  let f =
    {
      S.svar = too_few_formals_function_variable;
      sformals = [ count_mismatch_formal ];
      slocals = [];
      sbody = block [ stmt (S.Return (Some (int_const 0))) ];
    }
  in
  file
    [
      S.GFun f;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let too_many_formals_function_variable =
  global_var "f"
    (Language.Typ.TFun
       (int_t, Some [ ("x", int_t); ("y", int_t) ]))

let reject_function_too_many_formals =
  let f =
    {
      S.svar = too_many_formals_function_variable;
      sformals = [ count_mismatch_formal ];
      slocals = [];
      sbody = block [ stmt (S.Return (Some (int_const 0))) ];
    }
  in
  file
    [
      S.GFun f;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let reference_formal = local_var ~function_name:"f" "x" int_t

let reference_function =
  int_fun ~formals:[ reference_formal ] "f"
    [ stmt (S.Return (Some (var_exp reference_formal))) ]

let call_reference occurrence args =
  stmt (S.Instr [ S.Call (None, var_exp occurrence, args) ])

let accept_function_reference =
  file
    [
      S.GFun reference_function;
      S.GFun
        (main_fun
           [
             call_reference reference_function.S.svar [ int_const 1 ];
             stmt (S.Return (Some (int_const 0)));
           ]);
    ]

let mismatched_function_signature_occurrence =
  {
    reference_function.S.svar with
    S.vtype = Language.Typ.TFun (int_t, Some [ ("renamed", int_t) ]);
  }

let reject_function_occurrence_signature_mismatch =
  file
    [
      S.GFun reference_function;
      S.GFun
        (main_fun
           [
             call_reference mismatched_function_signature_occurrence
               [ int_const 1 ];
             stmt (S.Return (Some (int_const 0)));
           ]);
    ]

let mismatched_vglob_declaration =
  local_var ~function_name:"main" "x" int_t

let mismatched_vglob_occurrence =
  { mismatched_vglob_declaration with S.vglob = true }

let reject_variable_vglob_mismatch =
  file
    [
      S.GFun
        (main_fun ~locals:[ mismatched_vglob_declaration ]
           [ stmt (S.Return (Some (var_exp mismatched_vglob_occurrence))) ]);
    ]

let traversal_missing = global_var "missing" int_t

let main_returning exp =
  file [ S.GFun (main_fun [ stmt (S.Return (Some exp)) ]) ]

let reject_undeclared_in_unop =
  main_returning (S.Exp.UnOp (S.Exp.Neg, var_exp traversal_missing, int_t))

let reject_undeclared_in_binop =
  main_returning
    (S.Exp.BinOp
       (S.Exp.PlusA, int_const 1, var_exp traversal_missing, int_t))

let reject_undeclared_in_set_lval =
  file
    [
      S.GFun
        (main_fun
           [
             stmt
               (S.Instr
                  [
                    S.Set
                      ((S.Var traversal_missing, S.NoOffset), int_const 1);
                  ]);
             stmt (S.Return (Some (int_const 0)));
           ]);
    ]

let set_target = local_var ~function_name:"main" "x" int_t

let reject_undeclared_in_set_exp =
  file
    [
      S.GFun
        (main_fun ~locals:[ set_target ]
           [
             stmt
               (S.Instr
                  [
                    S.Set
                      ( (S.Var set_target, S.NoOffset),
                        var_exp traversal_missing );
                  ]);
             stmt (S.Return (Some (int_const 0)));
           ]);
    ]

let reject_undeclared_in_call_return_lval =
  file
    [
      S.GFun reference_function;
      S.GFun
        (main_fun
           [
             stmt
               (S.Instr
                  [
                    S.Call
                      ( Some (S.Var traversal_missing, S.NoOffset),
                        var_exp reference_function.S.svar,
                        [ int_const 1 ] );
                  ]);
             stmt (S.Return (Some (int_const 0)));
           ]);
    ]

let undeclared_function = function_var "missing_f" int_t []

let reject_undeclared_call_callee =
  file
    [
      S.GFun
        (main_fun
           [
             call_reference undeclared_function [];
             stmt (S.Return (Some (int_const 0)));
           ]);
    ]

let reject_undeclared_call_argument =
  file
    [
      S.GFun reference_function;
      S.GFun
        (main_fun
           [
             call_reference reference_function.S.svar
               [ var_exp traversal_missing ];
             stmt (S.Return (Some (int_const 0)));
           ]);
    ]

let reject_undeclared_if_condition =
  file
    [
      S.GFun
        (main_fun
           [
             stmt
               (S.If
                  (var_exp traversal_missing, block [], block []));
             stmt (S.Return (Some (int_const 0)));
           ]);
    ]

let reject_undeclared_if_then =
  file
    [
      S.GFun
        (main_fun
           [
             stmt
               (S.If
                  ( int_const 1,
                    block [ stmt (S.Return (Some (var_exp traversal_missing))) ],
                    block [] ));
             stmt (S.Return (Some (int_const 0)));
           ]);
    ]

let reject_undeclared_if_else =
  file
    [
      S.GFun
        (main_fun
           [
             stmt
               (S.If
                  ( int_const 0,
                    block [],
                    block [ stmt (S.Return (Some (var_exp traversal_missing))) ] ));
             stmt (S.Return (Some (int_const 0)));
           ]);
    ]

let reject_undeclared_in_loop =
  file
    [
      S.GFun
        (main_fun
           [
             stmt
               (S.Loop
                  (block
                     [ stmt (S.Return (Some (var_exp traversal_missing))) ]));
             stmt (S.Return (Some (int_const 0)));
           ]);
    ]

let reject_undeclared_in_block =
  file
    [
      S.GFun
        (main_fun
           [
             stmt
               (S.Block
                  (block
                     [ stmt (S.Return (Some (var_exp traversal_missing))) ]));
             stmt (S.Return (Some (int_const 0)));
           ]);
    ]

let reject_break_in_nested_if =
  file
    [
      S.GFun
        (main_fun
           [
             stmt
               (S.If
                  (int_const 1, block [ stmt S.Break ], block []));
             stmt (S.Return (Some (int_const 0)));
           ]);
    ]

let reject_continue_in_nested_block =
  file
    [
      S.GFun
        (main_fun
           [
             stmt (S.Block (block [ stmt S.Continue ]));
             stmt (S.Return (Some (int_const 0)));
           ]);
    ]

let reject_nested_return_value_in_void_function =
  let f =
    {
      S.svar = function_var "f" void_t [];
      sformals = [];
      slocals = [];
      sbody =
        block
          [
            stmt
              (S.If
                 ( int_const 1,
                   block [ stmt (S.Return (Some (int_const 1))) ],
                   block [] ));
          ];
    }
  in
  file
    [
      S.GFun f;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let reject_nested_return_without_value =
  let f =
    int_fun "f" [ stmt (S.Loop (block [ stmt (S.Return None) ])) ]
  in
  file
    [
      S.GFun f;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let reject_duplicate_function_and_global_name =
  let duplicate_global = global_var "f" int_t in
  let f = int_fun "f" [ stmt (S.Return (Some (int_const 0))) ] in
  file
    [
      S.GVarDecl duplicate_global;
      S.GFun f;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let reject_global_and_formal_same_name =
  let global_x = global_var "x" int_t in
  let formal_x = local_var ~function_name:"f" "x" int_t in
  let f =
    int_fun ~formals:[ formal_x ] "f"
      [ stmt (S.Return (Some (var_exp formal_x))) ]
  in
  file
    [
      S.GVarDecl global_x;
      S.GFun f;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let roundtrip_temp =
  local_var ~vtemp:true ~function_name:"main" "tmp" int_t

let reject_roundtrip_temp_loss =
  file
    [
      S.GFun
        (main_fun ~locals:[ roundtrip_temp ]
           [ stmt (S.Return (Some (var_exp roundtrip_temp))) ]);
    ]

let reject_goblint_call_arity =
  file
    [
      S.GFun reference_function;
      S.GFun
        (main_fun
           [
             call_reference reference_function.S.svar [];
             stmt (S.Return (Some (int_const 0)));
           ]);
    ]

let accept_uninitialized_global =
  let g = global_var "g" int_t in
  file
    [
      S.GVar (g, { init = None });
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let reject_block_return_value_in_void_function =
  let f =
    {
      S.svar = function_var "f" void_t [];
      sformals = [];
      slocals = [];
      sbody =
        block
          [
            stmt
              (S.Block
                 (block [ stmt (S.Return (Some (int_const 1))) ]));
          ];
    }
  in
  file
    [
      S.GFun f;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let reject_goblint_call_before_declaration =
  file
    [
      S.GFun
        (main_fun
           [
             call_reference reference_function.S.svar [ int_const 1 ];
             stmt (S.Return (Some (int_const 0)));
           ]);
      S.GFun reference_function;
    ]

let expect_ok name f =
  match SyntaxChecker.check_file f with
  | Ok () -> ()
  | Error err ->
      failwith
        (Printf.sprintf "%s: expected Ok, got %s" name
           (SyntaxChecker.string_of_error err))

let expect_error name expected f =
  match SyntaxChecker.check_file f with
  | Error actual when actual = expected -> ()
  | Error actual ->
      failwith
        (Printf.sprintf "%s: expected %s, got %s" name
           (SyntaxChecker.string_of_error expected)
           (SyntaxChecker.string_of_error actual))
  | Ok () ->
      failwith
        (Printf.sprintf "%s: expected %s, got Ok" name
           (SyntaxChecker.string_of_error expected))

let () =
  let cases =
    [
      ("accept_minimal_main", fun () -> expect_ok "accept_minimal_main" accept_minimal_main);
      ("reject_missing_main", fun () ->
        expect_error "reject_missing_main" SyntaxChecker.Missing_main
          reject_missing_main);
      ("reject_multiple_main", fun () ->
        expect_error "reject_multiple_main" SyntaxChecker.Multiple_main
          reject_multiple_main);
      ("reject_invalid_main_type", fun () ->
        expect_error "reject_invalid_main_type"
          (SyntaxChecker.Invalid_main_type void_t)
          reject_invalid_main_type);
      ("reject_main_with_parameters", fun () ->
        expect_error "reject_main_with_parameters"
          SyntaxChecker.Main_with_parameters reject_main_with_parameters);
      ("reject_duplicate_global_name", fun () ->
        expect_error "reject_duplicate_global_name"
          (SyntaxChecker.Duplicate_global_name "g")
          reject_duplicate_global_name);
      ("reject_duplicate_formal_name", fun () ->
        expect_error "reject_duplicate_formal_name"
          (SyntaxChecker.Duplicate_function_local_name
             { function_name = "f"; name = "x" })
          reject_duplicate_formal_name);
      ("reject_duplicate_local_name", fun () ->
        expect_error "reject_duplicate_local_name"
          (SyntaxChecker.Duplicate_function_local_name
             { function_name = "f"; name = "x" })
          reject_duplicate_local_name);
      ("reject_formal_local_name_collision", fun () ->
        expect_error "reject_formal_local_name_collision"
          (SyntaxChecker.Duplicate_function_local_name
             { function_name = "f"; name = "x" })
          reject_formal_local_name_collision);
      ("reject_break_outside_loop", fun () ->
        expect_error "reject_break_outside_loop" SyntaxChecker.Break_outside_loop
          reject_break_outside_loop);
      ("reject_continue_outside_loop", fun () ->
        expect_error "reject_continue_outside_loop"
          SyntaxChecker.Continue_outside_loop reject_continue_outside_loop);
      ("reject_return_value_in_void_function", fun () ->
        expect_error "reject_return_value_in_void_function"
          SyntaxChecker.Return_value_in_void_function
          reject_return_value_in_void_function);
      ("reject_return_without_value_in_nonvoid_function", fun () ->
        expect_error "reject_return_without_value_in_nonvoid_function"
          (SyntaxChecker.Return_without_value_in_nonvoid_function int_t)
          reject_return_without_value_in_nonvoid_function);
      ("accept_break_continue_inside_loop", fun () ->
        expect_ok "accept_break_continue_inside_loop"
          accept_break_continue_inside_loop);
      ("reject_invalid_global_scope", fun () ->
        expect_error "reject_invalid_global_scope"
          (SyntaxChecker.Invalid_variable_scope
             { variable = invalid_global_scope_var; expected = S.VarId.Global })
          reject_invalid_global_scope);
      ("reject_invalid_function_scope", fun () ->
        expect_error "reject_invalid_function_scope"
          (SyntaxChecker.Invalid_variable_scope
             {
               variable = invalid_function_scope_var;
               expected = S.VarId.Global;
             })
          reject_invalid_function_scope);
      ("reject_invalid_formal_scope", fun () ->
        expect_error "reject_invalid_formal_scope"
          (SyntaxChecker.Invalid_variable_scope
             {
               variable = invalid_formal_scope_var;
               expected = S.VarId.Function "f";
             })
          reject_invalid_formal_scope);
      ("reject_invalid_local_scope", fun () ->
        expect_error "reject_invalid_local_scope"
          (SyntaxChecker.Invalid_variable_scope
             {
               variable = invalid_local_scope_var;
               expected = S.VarId.Function "f";
             })
          reject_invalid_local_scope);
      ("reject_cross_function_reference", fun () ->
        expect_error "reject_cross_function_reference"
          (SyntaxChecker.Undeclared_variable cross_function_reference)
          reject_cross_function_reference);
      ("reject_variable_temp_mismatch", fun () ->
        expect_error "reject_variable_temp_mismatch"
          (SyntaxChecker.Variable_declaration_mismatch
             {
               occurrence = mismatched_temp_occurrence;
               declaration = mismatched_temp_declaration;
             })
          reject_variable_temp_mismatch);
      ("reject_undeclared_global_reference", fun () ->
        expect_error "reject_undeclared_global_reference"
          (SyntaxChecker.Undeclared_variable undeclared_global_reference)
          reject_undeclared_global_reference);
      ("reject_local_reference_in_global_initializer", fun () ->
        expect_error "reject_local_reference_in_global_initializer"
          (SyntaxChecker.Undeclared_variable initializer_local_reference)
          reject_local_reference_in_global_initializer);
      ("accept_same_local_name_in_different_functions", fun () ->
        expect_ok "accept_same_local_name_in_different_functions"
          accept_same_local_name_in_different_functions);
      ("reject_global_and_local_same_name", fun () ->
        expect_error "reject_global_and_local_same_name"
          (SyntaxChecker.Global_local_name_collision
             { function_name = "main"; name = "x" })
          reject_global_and_local_same_name);
      ("accept_global_reference", fun () ->
        expect_ok "accept_global_reference" accept_global_reference);
      ("reject_invalid_function_type", fun () ->
        expect_error "reject_invalid_function_type"
          (SyntaxChecker.Invalid_function_type invalid_function_type_var)
          reject_invalid_function_type);
      ("reject_incomplete_function_type", fun () ->
        expect_error "reject_incomplete_function_type"
          (SyntaxChecker.Function_formals_mismatch
             { function_variable = incomplete_function_variable; formals = [] })
          reject_incomplete_function_type);
      ("accept_multi_formal_function_signature", fun () ->
        expect_ok "accept_multi_formal_function_signature"
          accept_multi_formal_function_signature);
      ("reject_function_formal_name_mismatch", fun () ->
        expect_error "reject_function_formal_name_mismatch"
          (SyntaxChecker.Function_formals_mismatch
             {
               function_variable = name_mismatch_function_variable;
               formals = [ name_mismatch_formal ];
             })
          reject_function_formal_name_mismatch);
      ("reject_function_too_few_formals", fun () ->
        expect_error "reject_function_too_few_formals"
          (SyntaxChecker.Function_formals_mismatch
             {
               function_variable = too_few_formals_function_variable;
               formals = [ count_mismatch_formal ];
             })
          reject_function_too_few_formals);
      ("reject_function_too_many_formals", fun () ->
        expect_error "reject_function_too_many_formals"
          (SyntaxChecker.Function_formals_mismatch
             {
               function_variable = too_many_formals_function_variable;
               formals = [ count_mismatch_formal ];
             })
          reject_function_too_many_formals);
      ("accept_function_reference", fun () ->
        expect_ok "accept_function_reference" accept_function_reference);
      ("reject_function_occurrence_signature_mismatch", fun () ->
        expect_error "reject_function_occurrence_signature_mismatch"
          (SyntaxChecker.Variable_declaration_mismatch
             {
               occurrence = mismatched_function_signature_occurrence;
               declaration = reference_function.S.svar;
             })
          reject_function_occurrence_signature_mismatch);
      ("reject_variable_vglob_mismatch", fun () ->
        expect_error "reject_variable_vglob_mismatch"
          (SyntaxChecker.Variable_declaration_mismatch
             {
               occurrence = mismatched_vglob_occurrence;
               declaration = mismatched_vglob_declaration;
             })
          reject_variable_vglob_mismatch);
      ("reject_undeclared_in_unop", fun () ->
        expect_error "reject_undeclared_in_unop"
          (SyntaxChecker.Undeclared_variable traversal_missing)
          reject_undeclared_in_unop);
      ("reject_undeclared_in_binop", fun () ->
        expect_error "reject_undeclared_in_binop"
          (SyntaxChecker.Undeclared_variable traversal_missing)
          reject_undeclared_in_binop);
      ("reject_undeclared_in_set_lval", fun () ->
        expect_error "reject_undeclared_in_set_lval"
          (SyntaxChecker.Undeclared_variable traversal_missing)
          reject_undeclared_in_set_lval);
      ("reject_undeclared_in_set_exp", fun () ->
        expect_error "reject_undeclared_in_set_exp"
          (SyntaxChecker.Undeclared_variable traversal_missing)
          reject_undeclared_in_set_exp);
      ("reject_undeclared_in_call_return_lval", fun () ->
        expect_error "reject_undeclared_in_call_return_lval"
          (SyntaxChecker.Undeclared_variable traversal_missing)
          reject_undeclared_in_call_return_lval);
      ("reject_undeclared_call_callee", fun () ->
        expect_error "reject_undeclared_call_callee"
          (SyntaxChecker.Undeclared_variable undeclared_function)
          reject_undeclared_call_callee);
      ("reject_undeclared_call_argument", fun () ->
        expect_error "reject_undeclared_call_argument"
          (SyntaxChecker.Undeclared_variable traversal_missing)
          reject_undeclared_call_argument);
      ("reject_undeclared_if_condition", fun () ->
        expect_error "reject_undeclared_if_condition"
          (SyntaxChecker.Undeclared_variable traversal_missing)
          reject_undeclared_if_condition);
      ("reject_undeclared_if_then", fun () ->
        expect_error "reject_undeclared_if_then"
          (SyntaxChecker.Undeclared_variable traversal_missing)
          reject_undeclared_if_then);
      ("reject_undeclared_if_else", fun () ->
        expect_error "reject_undeclared_if_else"
          (SyntaxChecker.Undeclared_variable traversal_missing)
          reject_undeclared_if_else);
      ("reject_undeclared_in_loop", fun () ->
        expect_error "reject_undeclared_in_loop"
          (SyntaxChecker.Undeclared_variable traversal_missing)
          reject_undeclared_in_loop);
      ("reject_undeclared_in_block", fun () ->
        expect_error "reject_undeclared_in_block"
          (SyntaxChecker.Undeclared_variable traversal_missing)
          reject_undeclared_in_block);
      ("reject_break_in_nested_if", fun () ->
        expect_error "reject_break_in_nested_if"
          SyntaxChecker.Break_outside_loop reject_break_in_nested_if);
      ("reject_continue_in_nested_block", fun () ->
        expect_error "reject_continue_in_nested_block"
          SyntaxChecker.Continue_outside_loop reject_continue_in_nested_block);
      ("reject_nested_return_value_in_void_function", fun () ->
        expect_error "reject_nested_return_value_in_void_function"
          SyntaxChecker.Return_value_in_void_function
          reject_nested_return_value_in_void_function);
      ("reject_nested_return_without_value", fun () ->
        expect_error "reject_nested_return_without_value"
          (SyntaxChecker.Return_without_value_in_nonvoid_function int_t)
          reject_nested_return_without_value);
      ("reject_duplicate_function_and_global_name", fun () ->
        expect_error "reject_duplicate_function_and_global_name"
          (SyntaxChecker.Duplicate_global_name "f")
          reject_duplicate_function_and_global_name);
      ("reject_global_and_formal_same_name", fun () ->
        expect_error "reject_global_and_formal_same_name"
          (SyntaxChecker.Global_local_name_collision
             { function_name = "f"; name = "x" })
          reject_global_and_formal_same_name);
      ("reject_roundtrip_temp_loss", fun () ->
        expect_error "reject_roundtrip_temp_loss"
          (SyntaxChecker.Bridge_error
             (Language.CilBridge.Roundtrip_mismatch
                "CIL-- file changed after CIL-- -> CIL -> CIL--"))
          reject_roundtrip_temp_loss);
      ("reject_goblint_call_arity", fun () ->
        expect_error "reject_goblint_call_arity"
          SyntaxChecker.Goblint_check_failed reject_goblint_call_arity);
      ("accept_uninitialized_global", fun () ->
        expect_ok "accept_uninitialized_global" accept_uninitialized_global);
      ("reject_block_return_value_in_void_function", fun () ->
        expect_error "reject_block_return_value_in_void_function"
          SyntaxChecker.Return_value_in_void_function
          reject_block_return_value_in_void_function);
      ("reject_goblint_call_before_declaration", fun () ->
        expect_error "reject_goblint_call_before_declaration"
          SyntaxChecker.Goblint_check_failed
          reject_goblint_call_before_declaration);
    ]
  in
  List.iter
    (fun (name, run) ->
      run ();
      Printf.printf "ok - %s\n" name)
    cases
