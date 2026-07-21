open Language

module S = HoleSyntax
module C = HoleSyntaxChecker
module SC = SyntaxChecker

let int_t = Typ.TInt Typ.IInt
let uint_t = Typ.TInt Typ.IUInt
let void_t = Typ.TVoid

let global_var name typ : S.varinfo =
  { vtype = typ; vglob = true; vtemp = false; vid = S.VarId.global name }

let local_var ~function_name name typ : S.varinfo =
  {
    vtype = typ;
    vglob = false;
    vtemp = false;
    vid = S.VarId.local ~function_name name;
  }

let stmt skind : S.stmt = { labels = []; skind; sid = None }
let known skind = S.Stmt (stmt skind)
let block bstmts : S.block = { bstmts }

let int_const n =
  S.Exp.Const (Syntax.Exp.CInt (Int64.of_int n, Typ.IInt))

let var_exp var = S.Exp.Lval (S.Var var, S.NoOffset)

let function_type return_type formals =
  Typ.TFun
    ( return_type,
      Some
        (List.map
           (fun formal -> (SyntaxUtil.var_name formal, formal.vtype))
           formals) )

let function_var name return_type formals =
  global_var name (function_type return_type formals)

let fundec ?(return_type = int_t) ?(formals = []) ?(locals = []) name body :
    S.fundec =
  {
    svar = function_var name return_type formals;
    sformals = formals;
    slocals = locals;
    sbody = block body;
  }

let main ?(return_type = int_t) ?(formals = []) ?(locals = []) body =
  fundec ~return_type ~formals ~locals "main" body

let return_zero = known (S.Return (Some (int_const 0)))
let file globals : S.file = { fileName = "holesyntax-test.c"; globals }
let valid_main body = file [ S.GFun (main body) ]

let contains haystack needle =
  let haystack_length = String.length haystack in
  let needle_length = String.length needle in
  let rec loop index =
    if needle_length = 0 then true
    else if index + needle_length > haystack_length then false
    else if String.sub haystack index needle_length = needle then true
    else loop (index + 1)
  in
  loop 0

let expect_ok name = function
  | Ok () -> ()
  | Error error ->
      failwith
        (Printf.sprintf "%s: expected Ok, got %s" name
           (C.string_of_error error))

let expect_error name expected = function
  | Error actual when actual = expected -> ()
  | Error actual ->
      failwith
        (Printf.sprintf "%s: expected %s, got %s" name
           (C.string_of_error expected)
           (C.string_of_error actual))
  | Ok () ->
      failwith
        (Printf.sprintf "%s: expected %s, got Ok" name
           (C.string_of_error expected))

let expect_file_ok name file = expect_ok name (C.check_file file)
let expect_file_error name expected file =
  expect_error name expected (C.check_file file)

let test_accept_minimal_main () =
  expect_file_ok "accept_minimal_main" (valid_main [ return_zero ])

let test_accept_expression_hole () =
  expect_file_ok "accept_expression_hole"
    (valid_main [ known (S.Return (Some (S.ExpHole 1))) ])

let test_accept_whole_statement_sequence_hole () =
  expect_file_ok "accept_whole_statement_sequence_hole"
    (valid_main [ S.StmtSeqHole 1 ])

let test_accept_known_prefix_and_tail_hole () =
  let conditional =
    known (S.If (int_const 1, block [], block []))
  in
  expect_file_ok "accept_known_prefix_and_tail_hole"
    (valid_main [ conditional; S.StmtSeqHole 1 ])

let test_accept_distinct_hole_ids_in_one_ast () =
  let body =
    [
      known
        (S.If
           ( S.ExpHole 1,
             block [ known (S.Return (Some (S.ExpHole 2))) ],
             block [ return_zero ] ));
    ]
  in
  expect_file_ok "accept_distinct_hole_ids_in_one_ast" (valid_main body)

let test_accept_same_id_in_separate_ast_checks () =
  expect_ok "first_ast" (C.check_exp (S.ExpHole 1));
  expect_ok "second_ast" (C.check_exp (S.ExpHole 1))

let test_reject_repeated_expression_hole () =
  let body =
    [
      known
        (S.If
           ( S.ExpHole 1,
             block [ known (S.Return (Some (S.ExpHole 1))) ],
             block [ return_zero ] ));
    ]
  in
  expect_file_error "reject_repeated_expression_hole"
    (C.Duplicate_hole_id 1) (valid_main body)

let test_reject_repeated_statement_sequence_hole () =
  let body =
    [
      known
        (S.If
           (int_const 1, block [ S.StmtSeqHole 1 ], block [ S.StmtSeqHole 1 ]));
    ]
  in
  expect_file_error "reject_repeated_statement_sequence_hole"
    (C.Duplicate_hole_id 1) (valid_main body)

let test_accept_holes_in_nested_and_outer_blocks () =
  let inner = block [ S.StmtSeqHole 1 ] in
  let body = [ known (S.Block inner); S.StmtSeqHole 2 ] in
  expect_file_ok "accept_holes_in_nested_and_outer_blocks" (valid_main body)

let test_reject_nonpositive_expression_hole () =
  expect_error "reject_nonpositive_expression_hole" (C.Invalid_hole_id 0)
    (C.check_exp (S.ExpHole 0))

let test_reject_nonpositive_statement_sequence_hole () =
  expect_error "reject_nonpositive_statement_sequence_hole"
    (C.Invalid_hole_id (-1))
    (C.check_block (block [ S.StmtSeqHole (-1) ]))

let test_reject_hole_sort_mismatch () =
  let body =
    [
      known
        (S.If
           (S.ExpHole 1, block [ S.StmtSeqHole 1 ], block [ return_zero ]));
    ]
  in
  expect_file_error "reject_hole_sort_mismatch"
    (C.Hole_sort_mismatch
       { id = 1; expected = C.Expression; actual = C.Statement_sequence })
    (valid_main body)

let test_reject_multiple_direct_statement_sequence_holes () =
  expect_error "reject_multiple_direct_statement_sequence_holes"
    (C.Multiple_direct_stmt_seq_holes [ 1; 2 ])
    (C.check_block (block [ S.StmtSeqHole 1; S.StmtSeqHole 2 ]))

let test_reject_nonfinal_statement_sequence_hole () =
  expect_error "reject_nonfinal_statement_sequence_hole"
    (C.Nonfinal_stmt_seq_hole 1)
    (C.check_block (block [ S.StmtSeqHole 1; return_zero ]))

let test_reject_invalid_function_type () =
  let invalid_main = { (main [ return_zero ]) with svar = global_var "main" int_t } in
  expect_file_error "reject_invalid_function_type"
    (C.Syntax_error (SC.Invalid_function_type invalid_main.svar))
    (file [ S.GFun invalid_main ])

let test_reject_function_formals_mismatch () =
  let x = local_var ~function_name:"f" "x" int_t in
  let f =
    {
      (fundec "f" [ return_zero ]) with
      svar = function_var "f" int_t [];
      sformals = [ x ];
    }
  in
  expect_file_error "reject_function_formals_mismatch"
    (C.Syntax_error
       (SC.Function_formals_mismatch
          { function_variable = f.svar; formals = f.sformals }))
    (file [ S.GFun f; S.GFun (main [ return_zero ]) ])

let test_reject_missing_main () =
  expect_file_error "reject_missing_main" (C.Syntax_error SC.Missing_main)
    (file [])

let test_reject_multiple_main () =
  expect_file_error "reject_multiple_main" (C.Syntax_error SC.Multiple_main)
    (file [ S.GFun (main [ return_zero ]); S.GFun (main [ return_zero ]) ])

let test_reject_invalid_main_type () =
  expect_file_error "reject_invalid_main_type"
    (C.Syntax_error (SC.Invalid_main_type void_t))
    (file [ S.GFun (main ~return_type:void_t [ known (S.Return None) ]) ])

let test_reject_main_with_parameters () =
  let argc = local_var ~function_name:"main" "argc" int_t in
  expect_file_error "reject_main_with_parameters"
    (C.Syntax_error SC.Main_with_parameters)
    (file [ S.GFun (main ~formals:[ argc ] [ return_zero ]) ])

let test_reject_duplicate_global_name () =
  let first = global_var "g" int_t in
  let second = global_var "g" int_t in
  expect_file_error "reject_duplicate_global_name"
    (C.Syntax_error (SC.Duplicate_global_name "g"))
    (file
       [ S.GVarDecl first; S.GVarDecl second; S.GFun (main [ return_zero ]) ])

let test_reject_duplicate_local_name () =
  let first = local_var ~function_name:"main" "x" int_t in
  let second = local_var ~function_name:"main" "x" int_t in
  expect_file_error "reject_duplicate_local_name"
    (C.Syntax_error
       (SC.Duplicate_function_local_name
          { function_name = "main"; name = "x" }))
    (file [ S.GFun (main ~locals:[ first; second ] [ return_zero ]) ])

let test_reject_global_local_name_collision () =
  let global = global_var "x" int_t in
  let local = local_var ~function_name:"main" "x" int_t in
  expect_file_error "reject_global_local_name_collision"
    (C.Syntax_error
       (SC.Global_local_name_collision { function_name = "main"; name = "x" }))
    (file
       [ S.GVarDecl global; S.GFun (main ~locals:[ local ] [ return_zero ]) ])

let test_reject_invalid_global_scope () =
  let invalid_svar =
    local_var ~function_name:"main" "main" (function_type int_t [])
  in
  let invalid_main = { (main [ return_zero ]) with svar = invalid_svar } in
  expect_file_error "reject_invalid_global_scope"
    (C.Syntax_error
       (SC.Invalid_variable_scope
          { variable = invalid_svar; expected = S.VarId.Global }))
    (file [ S.GFun invalid_main ])

let test_reject_invalid_local_scope () =
  let invalid_local = global_var "x" int_t in
  expect_file_error "reject_invalid_local_scope"
    (C.Syntax_error
       (SC.Invalid_variable_scope
          {
            variable = invalid_local;
            expected = S.VarId.Function "main";
          }))
    (file [ S.GFun (main ~locals:[ invalid_local ] [ return_zero ]) ])

let test_reject_undeclared_known_variable () =
  let x = local_var ~function_name:"main" "x" int_t in
  expect_file_error "reject_undeclared_known_variable"
    (C.Syntax_error (SC.Undeclared_variable x))
    (valid_main [ known (S.Return (Some (var_exp x))) ])

let test_reject_variable_declaration_mismatch () =
  let declaration = local_var ~function_name:"main" "x" int_t in
  let occurrence = local_var ~function_name:"main" "x" uint_t in
  expect_file_error "reject_variable_declaration_mismatch"
    (C.Syntax_error
       (SC.Variable_declaration_mismatch { occurrence; declaration }))
    (file
       [
         S.GFun
           (main ~locals:[ declaration ]
              [ known (S.Return (Some (var_exp occurrence))) ]);
       ])

let test_reject_break_outside_loop () =
  expect_file_error "reject_break_outside_loop"
    (C.Syntax_error SC.Break_outside_loop)
    (valid_main [ known S.Break ])

let test_reject_continue_outside_loop () =
  expect_file_error "reject_continue_outside_loop"
    (C.Syntax_error SC.Continue_outside_loop)
    (valid_main [ known S.Continue ])

let test_accept_loop_control () =
  let loop_body = block [ known S.Continue; known S.Break ] in
  expect_file_ok "accept_loop_control"
    (valid_main [ known (S.Loop loop_body); return_zero ])

let test_reject_return_value_in_void_function () =
  let f = fundec ~return_type:void_t "f" [ return_zero ] in
  expect_file_error "reject_return_value_in_void_function"
    (C.Syntax_error SC.Return_value_in_void_function)
    (file [ S.GFun f; S.GFun (main [ return_zero ]) ])

let test_reject_return_without_value_in_nonvoid_function () =
  let f = fundec "f" [ known (S.Return None) ] in
  expect_file_error "reject_return_without_value_in_nonvoid_function"
    (C.Syntax_error (SC.Return_without_value_in_nonvoid_function int_t))
    (file [ S.GFun f; S.GFun (main [ return_zero ]) ])

let test_expression_string () =
  let actual = S.Exp.string_of_t (S.ExpHole 7) in
  if actual <> "?H7" then
    failwith (Printf.sprintf "expression_string: expected ?H7, got %s" actual)

let test_block_string () =
  let actual = S.string_of_block (block [ S.StmtSeqHole 2 ]) in
  let expected = "{\n  ...?H2\n}" in
  if actual <> expected then
    failwith
      (Printf.sprintf "block_string: expected %S, got %S" expected actual)

let test_pretty_output () =
  let conditional =
    known
      (S.If (S.ExpHole 1, block [ S.StmtSeqHole 2 ], block [ return_zero ]))
  in
  let output = HoleSyntaxPretty.string_of_file (valid_main [ conditional ]) in
  if not (contains output "ExpHole H1") then
    failwith "pretty_output: missing ExpHole H1";
  if not (contains output "StmtSeqHole H2") then
    failwith "pretty_output: missing StmtSeqHole H2"

let test_util_functions () =
  let source = valid_main [ S.StmtSeqHole 1 ] in
  match HoleSyntaxUtil.main_functions source with
  | [ main ] when HoleSyntaxUtil.function_return_type main = int_t -> ()
  | _ -> failwith "util_functions: main lookup or return type failed"

let () =
  let cases =
    [
      ("accept_minimal_main", test_accept_minimal_main);
      ("accept_expression_hole", test_accept_expression_hole);
      ( "accept_whole_statement_sequence_hole",
        test_accept_whole_statement_sequence_hole );
      ("accept_known_prefix_and_tail_hole", test_accept_known_prefix_and_tail_hole);
      ( "accept_distinct_hole_ids_in_one_ast",
        test_accept_distinct_hole_ids_in_one_ast );
      ( "accept_same_id_in_separate_ast_checks",
        test_accept_same_id_in_separate_ast_checks );
      ( "reject_repeated_expression_hole",
        test_reject_repeated_expression_hole );
      ( "reject_repeated_statement_sequence_hole",
        test_reject_repeated_statement_sequence_hole );
      ( "accept_holes_in_nested_and_outer_blocks",
        test_accept_holes_in_nested_and_outer_blocks );
      ("reject_nonpositive_expression_hole", test_reject_nonpositive_expression_hole);
      ( "reject_nonpositive_statement_sequence_hole",
        test_reject_nonpositive_statement_sequence_hole );
      ("reject_hole_sort_mismatch", test_reject_hole_sort_mismatch);
      ( "reject_multiple_direct_statement_sequence_holes",
        test_reject_multiple_direct_statement_sequence_holes );
      ( "reject_nonfinal_statement_sequence_hole",
        test_reject_nonfinal_statement_sequence_hole );
      ("reject_invalid_function_type", test_reject_invalid_function_type);
      ("reject_function_formals_mismatch", test_reject_function_formals_mismatch);
      ("reject_missing_main", test_reject_missing_main);
      ("reject_multiple_main", test_reject_multiple_main);
      ("reject_invalid_main_type", test_reject_invalid_main_type);
      ("reject_main_with_parameters", test_reject_main_with_parameters);
      ("reject_duplicate_global_name", test_reject_duplicate_global_name);
      ("reject_duplicate_local_name", test_reject_duplicate_local_name);
      ("reject_global_local_name_collision", test_reject_global_local_name_collision);
      ("reject_invalid_global_scope", test_reject_invalid_global_scope);
      ("reject_invalid_local_scope", test_reject_invalid_local_scope);
      ("reject_undeclared_known_variable", test_reject_undeclared_known_variable);
      ( "reject_variable_declaration_mismatch",
        test_reject_variable_declaration_mismatch );
      ("reject_break_outside_loop", test_reject_break_outside_loop);
      ("reject_continue_outside_loop", test_reject_continue_outside_loop);
      ("accept_loop_control", test_accept_loop_control);
      ( "reject_return_value_in_void_function",
        test_reject_return_value_in_void_function );
      ( "reject_return_without_value_in_nonvoid_function",
        test_reject_return_without_value_in_nonvoid_function );
      ("expression_string", test_expression_string);
      ("block_string", test_block_string);
      ("pretty_output", test_pretty_output);
      ("util_functions", test_util_functions);
    ]
  in
  List.iter
    (fun (name, run) ->
      run ();
      Printf.printf "ok - %s\n" name)
    cases
