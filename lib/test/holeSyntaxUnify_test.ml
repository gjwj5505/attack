open Language

module S = Syntax
module Sub = HoleSubstitution
module U = HoleSyntaxUnify

let int_t = Typ.TInt Typ.IInt

let int_const n =
  S.Const (Syntax.Exp.CInt (Int64.of_int n, Typ.IInt))

let plus left right = S.BinOp (Syntax.PlusA, left, right, int_t)

let global_var name typ : S.varinfo =
  { vtype = typ; vglob = true; vtemp = false; vid = S.VarId.global name }

let var_exp var = S.Lval (S.Var var, S.NoOffset)
let lval var = (S.Var var, S.NoOffset)
let stmt ?(labels = []) ?sid skind : S.holed S.stmt =
  { labels; skind; sid }
let known ?(labels = []) ?sid skind = S.Stmt (stmt ~labels ?sid skind)
let return exp = known (S.Return (Some exp))
let block bstmts : S.holed S.block = { bstmts }

let function_type return_type formals =
  Typ.TFun
    ( return_type,
      Some
        (List.map
           (fun formal -> (SyntaxUtil.var_name formal, formal.vtype))
           formals) )

let fundec ?(formals = []) ?(locals = []) name body : S.holed S.fundec =
  {
    svar = global_var name (function_type int_t formals);
    sformals = formals;
    slocals = locals;
    sbody = block body;
  }

let file globals : S.holed S.file =
  { fileName = "unify-test.c"; globals }

let expect_ok name = function
  | Ok substitution -> substitution
  | Error error ->
      failwith
        (Printf.sprintf "%s: expected Ok, got %s" name
           (U.string_of_error error))

let expect_sub_ok name = function
  | Ok substitution -> substitution
  | Error error ->
      failwith
        (Printf.sprintf "%s: expected Ok, got %s" name
           (Sub.string_of_error error))

let expect_error name expected = function
  | Error actual when actual = expected -> ()
  | Error actual ->
      failwith
        (Printf.sprintf "%s: expected %s, got %s" name
           (U.string_of_error expected)
           (U.string_of_error actual))
  | Ok substitution ->
      failwith
        (Printf.sprintf "%s: expected %s, got %s" name
           (U.string_of_error expected)
           (Sub.string_of_t substitution))

let expect_error_where name describe predicate = function
  | Error error when predicate error -> ()
  | Error error ->
      failwith
        (Printf.sprintf "%s: expected %s, got %s" name describe
           (U.string_of_error error))
  | Ok substitution ->
      failwith
        (Printf.sprintf "%s: expected %s, got %s" name describe
           (Sub.string_of_t substitution))

let expect_well_formed name substitution =
  match Sub.check_well_formed substitution with
  | Ok () -> ()
  | Error error ->
      failwith
        (Printf.sprintf "%s: malformed substitution: %s" name
           (Sub.string_of_invariant_error error))

let expect_empty name (substitution : Sub.t) =
  if
    not
      (Sub.HoleIdMap.is_empty substitution.exps
      && Sub.HoleIdMap.is_empty substitution.stmt_seqs)
  then
    failwith
      (Printf.sprintf "%s: expected empty substitution, got %s" name
         (Sub.string_of_t substitution))

let expect_exp name expected actual =
  if actual <> expected then
    failwith
      (Printf.sprintf "%s: expected %s, got %s" name
         (S.Exp.string_of_t expected)
         (S.Exp.string_of_t actual))

let expect_stmt_seq name expected actual =
  if actual <> expected then
    failwith
      (Printf.sprintf "%s: expected %s, got %s" name
         (Sub.string_of_stmt_seq expected)
         (Sub.string_of_stmt_seq actual))

let find_exp name hole substitution =
  match Sub.find_exp hole substitution with
  | Some exp -> exp
  | None -> failwith (Printf.sprintf "%s: missing expression binding H%d" name hole)

let find_stmt_seq name hole substitution =
  match Sub.find_stmt_seq hole substitution with
  | Some stmt_seq -> stmt_seq
  | None ->
      failwith
        (Printf.sprintf "%s: missing statement-sequence binding H%d" name hole)

let expect_exp_solution name substitution left right =
  let left = Sub.apply_exp substitution left in
  let right = Sub.apply_exp substitution right in
  if left <> right then
    failwith
      (Printf.sprintf "%s: unification result differs after apply: %s <> %s"
         name (S.Exp.string_of_t left) (S.Exp.string_of_t right))

let expect_stmt_seq_solution name substitution left right =
  let left = Sub.apply_stmt_seq substitution left in
  let right = Sub.apply_stmt_seq substitution right in
  if left <> right then
    failwith
      (Printf.sprintf "%s: unification result differs after apply: %s <> %s"
         name (Sub.string_of_stmt_seq left) (Sub.string_of_stmt_seq right))

let expect_ast_solution name substitution left right =
  let left = Sub.apply_ast substitution left in
  let right = Sub.apply_ast substitution right in
  if left <> right then
    failwith (name ^ ": ASTs differ after applying unification result")

let test_equal_expression_returns_empty () =
  let exp = plus (int_const 1) (int_const 2) in
  let substitution = expect_ok "equal_expression" (U.unify_exp exp exp) in
  expect_empty "equal_expression" substitution;
  expect_well_formed "equal_expression" substitution

let test_bind_fresh_expression_hole () =
  let left = S.ExpHole 1 in
  let right = plus (int_const 2) (int_const 3) in
  let substitution = expect_ok "fresh_exp_hole" (U.unify_exp left right) in
  expect_exp "fresh_exp_hole" right
    (find_exp "fresh_exp_hole" 1 substitution);
  expect_exp_solution "fresh_exp_hole" substitution left right;
  expect_well_formed "fresh_exp_hole" substitution

let test_expression_holes_use_canonical_id () =
  let left = S.ExpHole 2 in
  let right = S.ExpHole 1 in
  let substitution = expect_ok "canonical_exp_hole" (U.unify_exp left right) in
  expect_exp "canonical_exp_hole" (S.ExpHole 1)
    (find_exp "canonical_exp_hole" 2 substitution);
  if Sub.find_exp 1 substitution <> None then
    failwith "canonical_exp_hole: smaller ID should remain unbound";
  expect_exp_solution "canonical_exp_hole" substitution left right;
  expect_well_formed "canonical_exp_hole" substitution

let test_recursive_expression_refinement () =
  let initial =
    expect_sub_ok "recursive_exp initial"
      (Sub.bind_exp Sub.empty 1 (plus (S.ExpHole 2) (int_const 1)))
  in
  let left = S.ExpHole 1 in
  let right = plus (int_const 3) (int_const 1) in
  let substitution =
    expect_ok "recursive_exp"
      (U.unify_exp_under initial left right)
  in
  expect_exp "recursive_exp H2" (int_const 3)
    (find_exp "recursive_exp" 2 substitution);
  expect_exp "recursive_exp H1" right
    (find_exp "recursive_exp" 1 substitution);
  expect_exp_solution "recursive_exp" substitution left right;
  expect_well_formed "recursive_exp" substitution

let test_reject_expression_mismatch () =
  let left = int_const 1 in
  let right = int_const 2 in
  expect_error "expression_mismatch" (U.Expression_mismatch (left, right))
    (U.unify_exp left right)

let test_reject_expression_occurs_check () =
  let left = S.ExpHole 1 in
  let right = plus (S.ExpHole 1) (int_const 1) in
  expect_error "expression_occurs"
    (U.Substitution_error (Sub.Occurs_check_failed 1))
    (U.unify_exp left right)

let test_set_unifies_expression () =
  let x = global_var "x" int_t in
  let left = S.Set (lval x, S.ExpHole 1) in
  let right = S.Set (lval x, int_const 4) in
  let substitution = expect_ok "set" (U.unify_instr left right) in
  expect_exp "set" (int_const 4) (find_exp "set" 1 substitution);
  expect_well_formed "set" substitution

let test_call_unifies_arguments_in_order () =
  let f = global_var "f" (function_type int_t []) in
  let left =
    S.Call (None, var_exp f, [ S.ExpHole 1; plus (S.ExpHole 2) (int_const 1) ])
  in
  let right =
    S.Call (None, var_exp f, [ int_const 5; plus (int_const 6) (int_const 1) ])
  in
  let substitution = expect_ok "call_arguments" (U.unify_instr left right) in
  expect_exp "call_arguments H1" (int_const 5)
    (find_exp "call_arguments" 1 substitution);
  expect_exp "call_arguments H2" (int_const 6)
    (find_exp "call_arguments" 2 substitution);
  expect_well_formed "call_arguments" substitution

let test_reject_call_argument_length_mismatch () =
  let f = global_var "f" (function_type int_t []) in
  let left = S.Call (None, var_exp f, [ int_const 1 ]) in
  let right = S.Call (None, var_exp f, []) in
  expect_error "call_argument_length"
    (U.Instruction_mismatch (left, right))
    (U.unify_instr left right)

let test_statement_ignores_sid () =
  let left = stmt ~sid:1 S.Break in
  let right = stmt ~sid:2 S.Break in
  let substitution = expect_ok "ignore_sid" (U.unify_stmt left right) in
  expect_empty "ignore_sid" substitution;
  expect_well_formed "ignore_sid" substitution

let test_reject_statement_label_mismatch () =
  let left = stmt ~labels:[ Syntax.Label "left" ] S.Break in
  let right = stmt ~labels:[ Syntax.Label "right" ] S.Break in
  expect_error "label_mismatch" (U.Statement_mismatch (left, right))
    (U.unify_stmt left right)

let test_reject_instruction_list_length_mismatch () =
  let x = global_var "x" int_t in
  let left = stmt (S.Instr [ S.Set (lval x, int_const 1) ]) in
  let right = stmt (S.Instr []) in
  expect_error "instruction_list_length"
    (U.Instruction_list_mismatch
       ([ S.Set (lval x, int_const 1) ], []))
    (U.unify_stmt left right)

let test_tail_hole_binds_remaining_sequence () =
  let first = known S.Break in
  let second = known S.Continue in
  let third = return (int_const 3) in
  let left = [ first; S.StmtSeqHole 1 ] in
  let right = [ first; second; third ] in
  let substitution = expect_ok "tail_remaining" (U.unify_stmt_seq left right) in
  expect_stmt_seq "tail_remaining binding" [ second; third ]
    (find_stmt_seq "tail_remaining" 1 substitution);
  expect_stmt_seq_solution "tail_remaining" substitution left right;
  expect_well_formed "tail_remaining" substitution

let test_tail_hole_binds_empty_sequence () =
  let first = known S.Break in
  let left = [ first; S.StmtSeqHole 1 ] in
  let right = [ first ] in
  let substitution = expect_ok "tail_empty" (U.unify_stmt_seq left right) in
  expect_stmt_seq "tail_empty binding" []
    (find_stmt_seq "tail_empty" 1 substitution);
  expect_stmt_seq_solution "tail_empty" substitution left right;
  expect_well_formed "tail_empty" substitution

let test_statement_sequence_holes_use_canonical_id () =
  let left = [ S.StmtSeqHole 2 ] in
  let right = [ S.StmtSeqHole 1 ] in
  let substitution =
    expect_ok "canonical_stmt_seq_hole" (U.unify_stmt_seq left right)
  in
  expect_stmt_seq "canonical_stmt_seq_hole binding" [ S.StmtSeqHole 1 ]
    (find_stmt_seq "canonical_stmt_seq_hole" 2 substitution);
  if Sub.find_stmt_seq 1 substitution <> None then
    failwith "canonical_stmt_seq_hole: smaller ID should remain unbound";
  expect_stmt_seq_solution "canonical_stmt_seq_hole" substitution left right;
  expect_well_formed "canonical_stmt_seq_hole" substitution

let test_recursive_statement_sequence_refinement () =
  let initial_rhs =
    [ return (S.ExpHole 2); S.StmtSeqHole 3 ]
  in
  let initial =
    expect_sub_ok "recursive_stmt_seq initial"
      (Sub.bind_stmt_seq Sub.empty 1 initial_rhs)
  in
  let left = [ S.StmtSeqHole 1 ] in
  let right = [ return (int_const 4); known S.Break ] in
  let substitution =
    expect_ok "recursive_stmt_seq"
      (U.unify_stmt_seq_under initial left right)
  in
  expect_exp "recursive_stmt_seq H2" (int_const 4)
    (find_exp "recursive_stmt_seq" 2 substitution);
  expect_stmt_seq "recursive_stmt_seq H3" [ known S.Break ]
    (find_stmt_seq "recursive_stmt_seq" 3 substitution);
  expect_stmt_seq "recursive_stmt_seq H1" right
    (find_stmt_seq "recursive_stmt_seq" 1 substitution);
  expect_stmt_seq_solution "recursive_stmt_seq" substitution left right;
  expect_well_formed "recursive_stmt_seq" substitution

let test_reject_statement_sequence_occurs_check () =
  let left = [ S.StmtSeqHole 1 ] in
  let right = [ known (S.Block (block [ S.StmtSeqHole 1 ])) ] in
  expect_error "stmt_seq_occurs"
    (U.Substitution_error (Sub.Occurs_check_failed 1))
    (U.unify_stmt_seq left right)

let test_reject_statement_sequence_length_mismatch () =
  let first = known S.Break in
  let second = known S.Continue in
  expect_error_where "stmt_seq_length" "statement-sequence mismatch"
    (function U.Statement_sequence_mismatch _ -> true | _ -> false)
    (U.unify_stmt_seq [ first ] [ first; second ])

let test_reject_cross_sort_hole_id () =
  let left = [ return (S.ExpHole 1) ] in
  let right = [ return (int_const 7); S.StmtSeqHole 1 ] in
  expect_error "cross_sort_hole"
    (U.Substitution_error
       (Sub.Sort_mismatch
          { hole = 1; expected = Sub.StmtSeq; actual = Sub.Exp }))
    (U.unify_stmt_seq left right)

let test_compound_initializer_unifies_recursively () =
  let left =
    S.CompoundInit
      ( int_t,
        [
          ( S.Index (S.ExpHole 1, S.NoOffset),
            S.SingleInit (S.ExpHole 2) );
        ] )
  in
  let right =
    S.CompoundInit
      ( int_t,
        [
          ( S.Index (int_const 0, S.NoOffset),
            S.SingleInit (int_const 8) );
        ] )
  in
  let substitution = expect_ok "compound_init" (U.unify_init left right) in
  expect_exp "compound_init H1" (int_const 0)
    (find_exp "compound_init" 1 substitution);
  expect_exp "compound_init H2" (int_const 8)
    (find_exp "compound_init" 2 substitution);
  expect_well_formed "compound_init" substitution

let test_file_unifies_nested_function_body () =
  let left =
    file [ S.GFun (fundec "main" [ return (S.ExpHole 1) ]) ]
  in
  let right =
    file [ S.GFun (fundec "main" [ return (int_const 9) ]) ]
  in
  let substitution = expect_ok "file" (U.unify_file left right) in
  expect_exp "file H1" (int_const 9) (find_exp "file" 1 substitution);
  expect_ast_solution "file" substitution (S.AFile left) (S.AFile right);
  expect_well_formed "file" substitution

let test_ast_dispatches_initializer () =
  let left = S.AInit (S.SingleInit (S.ExpHole 1)) in
  let right = S.AInit (S.SingleInit (int_const 10)) in
  let substitution = expect_ok "ast_init" (U.unify_ast left right) in
  expect_exp "ast_init H1" (int_const 10)
    (find_exp "ast_init" 1 substitution);
  expect_ast_solution "ast_init" substitution left right;
  expect_well_formed "ast_init" substitution

let test_reject_different_ast_kinds () =
  let left = S.AExp (int_const 1) in
  let right = S.AInit (S.SingleInit (int_const 1)) in
  expect_error "ast_kind" (U.Ast_mismatch (left, right))
    (U.unify_ast left right)

let () =
  let cases =
    [
      ("equal_expression_returns_empty", test_equal_expression_returns_empty);
      ("bind_fresh_expression_hole", test_bind_fresh_expression_hole);
      ( "expression_holes_use_canonical_id",
        test_expression_holes_use_canonical_id );
      ("recursive_expression_refinement", test_recursive_expression_refinement);
      ("reject_expression_mismatch", test_reject_expression_mismatch);
      ("reject_expression_occurs_check", test_reject_expression_occurs_check);
      ("set_unifies_expression", test_set_unifies_expression);
      ("call_unifies_arguments_in_order", test_call_unifies_arguments_in_order);
      ( "reject_call_argument_length_mismatch",
        test_reject_call_argument_length_mismatch );
      ("statement_ignores_sid", test_statement_ignores_sid);
      ("reject_statement_label_mismatch", test_reject_statement_label_mismatch);
      ( "reject_instruction_list_length_mismatch",
        test_reject_instruction_list_length_mismatch );
      ( "tail_hole_binds_remaining_sequence",
        test_tail_hole_binds_remaining_sequence );
      ("tail_hole_binds_empty_sequence", test_tail_hole_binds_empty_sequence);
      ( "statement_sequence_holes_use_canonical_id",
        test_statement_sequence_holes_use_canonical_id );
      ( "recursive_statement_sequence_refinement",
        test_recursive_statement_sequence_refinement );
      ( "reject_statement_sequence_occurs_check",
        test_reject_statement_sequence_occurs_check );
      ( "reject_statement_sequence_length_mismatch",
        test_reject_statement_sequence_length_mismatch );
      ("reject_cross_sort_hole_id", test_reject_cross_sort_hole_id);
      ( "compound_initializer_unifies_recursively",
        test_compound_initializer_unifies_recursively );
      ("file_unifies_nested_function_body", test_file_unifies_nested_function_body);
      ("ast_dispatches_initializer", test_ast_dispatches_initializer);
      ("reject_different_ast_kinds", test_reject_different_ast_kinds);
    ]
  in
  List.iter
    (fun (name, run) ->
      run ();
      Printf.printf "ok - %s\n" name)
    cases
