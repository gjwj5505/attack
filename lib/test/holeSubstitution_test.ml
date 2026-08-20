open Language

module S = Syntax
module Sub = HoleSubstitution

let int_t = Typ.TInt Typ.IInt

let int_const n =
  S.Const (Syntax.Exp.CInt (Int64.of_int n, Typ.IInt))

let plus left right = S.BinOp (Syntax.PlusA, left, right, int_t)
let stmt skind : S.holed S.stmt = { labels = []; skind; sid = None }
let known skind = S.Stmt (stmt skind)
let return exp = known (S.Return (Some exp))
let block bstmts : S.holed S.block = { bstmts }

let map_of_bindings bindings =
  List.fold_left
    (fun map (hole, rhs) -> Sub.HoleIdMap.add hole rhs map)
    Sub.HoleIdMap.empty bindings

let substitution ?(exps = []) ?(stmt_seqs = []) () : Sub.t =
  {
    exps = map_of_bindings exps;
    stmt_seqs = map_of_bindings stmt_seqs;
  }

let expect_ok name = function
  | Ok value -> value
  | Error error ->
      failwith
        (Printf.sprintf "%s: expected Ok, got %s" name
           (Sub.string_of_error error))

let expect_error name expected = function
  | Error actual when actual = expected -> ()
  | Error actual ->
      failwith
        (Printf.sprintf "%s: expected %s, got %s" name
           (Sub.string_of_error expected)
           (Sub.string_of_error actual))
  | Ok substitution ->
      failwith
        (Printf.sprintf "%s: expected %s, got %s" name
           (Sub.string_of_error expected)
           (Sub.string_of_t substitution))

let expect_well_formed name substitution =
  match Sub.check_well_formed substitution with
  | Ok () -> ()
  | Error error ->
      failwith
        (Printf.sprintf "%s: expected a well-formed substitution, got %s"
           name (Sub.string_of_invariant_error error))

let expect_invariant_error name expected substitution =
  match Sub.check_well_formed substitution with
  | Error actual when actual = expected -> ()
  | Error actual ->
      failwith
        (Printf.sprintf "%s: expected %s, got %s" name
           (Sub.string_of_invariant_error expected)
           (Sub.string_of_invariant_error actual))
  | Ok () ->
      failwith
        (Printf.sprintf "%s: expected %s, got Ok" name
           (Sub.string_of_invariant_error expected))

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
  | Some items -> items
  | None ->
      failwith
        (Printf.sprintf "%s: missing statement-sequence binding H%d" name hole)

let test_apply_exp_nested () =
  let substitution =
    substitution ~exps:[ (1, int_const 1); (2, int_const 2) ] ()
  in
  let input = plus (S.ExpHole 1) (plus (S.ExpHole 2) (S.ExpHole 3)) in
  let expected = plus (int_const 1) (plus (int_const 2) (S.ExpHole 3)) in
  expect_exp "apply_exp_nested" expected (Sub.apply_exp substitution input)

let test_apply_stmt_seq_splices_tail () =
  let replacement = [ return (int_const 2); S.StmtSeqHole 3 ] in
  let substitution =
    substitution ~exps:[ (1, int_const 1) ]
      ~stmt_seqs:[ (2, replacement) ] ()
  in
  let input = [ return (S.ExpHole 1); S.StmtSeqHole 2 ] in
  let expected = [ return (int_const 1); return (int_const 2); S.StmtSeqHole 3 ] in
  expect_stmt_seq "apply_stmt_seq_splices_tail" expected
    (Sub.apply_stmt_seq substitution input)

let test_apply_nested_block () =
  let replacement = [ return (int_const 4) ] in
  let substitution = substitution ~stmt_seqs:[ (2, replacement) ] () in
  let input = block [ known (S.Block (block [ S.StmtSeqHole 2 ])) ] in
  let expected = block [ known (S.Block (block replacement)) ] in
  if Sub.apply_block substitution input <> expected then
    failwith "apply_nested_block: nested tail hole was not replaced"

let test_apply_ast () =
  let substitution = substitution ~exps:[ (1, int_const 7) ] () in
  let input = S.AInit (S.SingleInit (S.ExpHole 1)) in
  let expected = S.AInit (S.SingleInit (int_const 7)) in
  if Sub.apply_ast substitution input <> expected then
    failwith "apply_ast: initializer hole was not replaced"

let test_bind_normalizes_new_rhs () =
  let substitution =
    Sub.empty
    |> fun substitution -> expect_ok "bind H1" (Sub.bind_exp substitution 1 (int_const 1))
    |> fun substitution ->
    expect_ok "bind H2"
      (Sub.bind_exp substitution 2 (plus (S.ExpHole 1) (S.ExpHole 3)))
  in
  expect_exp "bind_normalizes_new_rhs"
    (plus (int_const 1) (S.ExpHole 3))
    (find_exp "bind_normalizes_new_rhs" 2 substitution);
  expect_well_formed "bind_normalizes_new_rhs" substitution

let test_bind_updates_old_rhs () =
  let substitution =
    expect_ok "bind H1" (Sub.bind_exp Sub.empty 1 (S.ExpHole 2))
  in
  let substitution =
    expect_ok "bind H2" (Sub.bind_exp substitution 2 (int_const 8))
  in
  expect_exp "bind_updates_old_rhs" (int_const 8)
    (find_exp "bind_updates_old_rhs" 1 substitution);
  expect_well_formed "bind_updates_old_rhs" substitution

let test_exp_bind_updates_stmt_seq_rhs () =
  let substitution =
    expect_ok "bind stmt H2"
      (Sub.bind_stmt_seq Sub.empty 2 [ return (S.ExpHole 1) ])
  in
  let substitution =
    expect_ok "bind exp H1" (Sub.bind_exp substitution 1 (int_const 9))
  in
  expect_stmt_seq "exp_bind_updates_stmt_seq_rhs" [ return (int_const 9) ]
    (find_stmt_seq "exp_bind_updates_stmt_seq_rhs" 2 substitution);
  expect_well_formed "exp_bind_updates_stmt_seq_rhs" substitution

let test_stmt_seq_bind_updates_old_rhs () =
  let substitution =
    expect_ok "bind stmt H1"
      (Sub.bind_stmt_seq Sub.empty 1 [ S.StmtSeqHole 2 ])
  in
  let substitution =
    expect_ok "bind stmt H2"
      (Sub.bind_stmt_seq substitution 2 [ known S.Break ])
  in
  expect_stmt_seq "stmt_seq_bind_updates_old_rhs" [ known S.Break ]
    (find_stmt_seq "stmt_seq_bind_updates_old_rhs" 1 substitution);
  expect_well_formed "stmt_seq_bind_updates_old_rhs" substitution

let test_reject_direct_exp_occurs () =
  expect_error "reject_direct_exp_occurs" (Sub.Occurs_check_failed 1)
    (Sub.bind_exp Sub.empty 1 (plus (S.ExpHole 1) (int_const 1)))

let test_reject_indirect_exp_occurs () =
  let substitution =
    expect_ok "bind H2"
      (Sub.bind_exp Sub.empty 2 (plus (S.ExpHole 1) (int_const 1)))
  in
  expect_error "reject_indirect_exp_occurs" (Sub.Occurs_check_failed 1)
    (Sub.bind_exp substitution 1 (S.ExpHole 2))

let test_reject_direct_stmt_seq_occurs () =
  expect_error "reject_direct_stmt_seq_occurs" (Sub.Occurs_check_failed 1)
    (Sub.bind_stmt_seq Sub.empty 1 [ S.StmtSeqHole 1 ])

let test_reject_indirect_stmt_seq_occurs () =
  let substitution =
    expect_ok "bind stmt H2"
      (Sub.bind_stmt_seq Sub.empty 2 [ S.StmtSeqHole 1 ])
  in
  expect_error "reject_indirect_stmt_seq_occurs" (Sub.Occurs_check_failed 1)
    (Sub.bind_stmt_seq substitution 1 [ S.StmtSeqHole 2 ])

let test_reject_already_bound () =
  let substitution =
    expect_ok "bind H1" (Sub.bind_exp Sub.empty 1 (int_const 1))
  in
  expect_error "reject_already_bound" (Sub.Already_bound 1)
    (Sub.bind_exp substitution 1 (int_const 2))

let test_reject_sort_mismatch () =
  let substitution =
    expect_ok "bind stmt H1" (Sub.bind_stmt_seq Sub.empty 1 [])
  in
  expect_error "reject_sort_mismatch"
    (Sub.Sort_mismatch { hole = 1; expected = Sub.Exp; actual = Sub.StmtSeq })
    (Sub.bind_exp substitution 1 (int_const 1))

let test_reject_inconsistent_domains_on_bind () =
  let substitution =
    substitution ~exps:[ (1, int_const 1) ] ~stmt_seqs:[ (1, []) ] ()
  in
  expect_error "reject_inconsistent_domains_on_bind"
    (Sub.Inconsistent_domains 1)
    (Sub.bind_exp substitution 1 (int_const 2))

let test_fold_bind () =
  let bindings =
    map_of_bindings [ (1, S.ExpHole 2); (2, int_const 5) ]
  in
  let substitution =
    expect_ok "fold_bind" (Sub.fold_bind Sub.bind_exp bindings Sub.empty)
  in
  expect_exp "fold_bind H1" (int_const 5)
    (find_exp "fold_bind" 1 substitution);
  expect_well_formed "fold_bind" substitution

let test_compose_direction () =
  let before =
    expect_ok "before" (Sub.bind_exp Sub.empty 1 (S.ExpHole 2))
  in
  let after =
    expect_ok "after" (Sub.bind_exp Sub.empty 2 (int_const 6))
  in
  let composed = expect_ok "compose" (Sub.compose ~after ~before) in
  expect_exp "compose H1" (int_const 6) (find_exp "compose" 1 composed);
  expect_exp "compose H2" (int_const 6) (find_exp "compose" 2 composed);
  expect_well_formed "compose" composed

let test_compose_exp_into_stmt_seq () =
  let before =
    expect_ok "before"
      (Sub.bind_stmt_seq Sub.empty 2 [ return (S.ExpHole 1) ])
  in
  let after =
    expect_ok "after" (Sub.bind_exp Sub.empty 1 (int_const 3))
  in
  let composed = expect_ok "compose" (Sub.compose ~after ~before) in
  expect_stmt_seq "compose_exp_into_stmt_seq" [ return (int_const 3) ]
    (find_stmt_seq "compose_exp_into_stmt_seq" 2 composed)

let test_compose_rejects_overlapping_domain () =
  let before =
    expect_ok "before" (Sub.bind_exp Sub.empty 1 (int_const 1))
  in
  let after =
    expect_ok "after" (Sub.bind_exp Sub.empty 1 (int_const 2))
  in
  expect_error "compose_rejects_overlapping_domain" (Sub.Already_bound 1)
    (Sub.compose ~after ~before)

let test_accept_shared_unbound_range_hole () =
  let substitution =
    substitution ~exps:[ (1, S.ExpHole 3); (2, S.ExpHole 3) ] ()
  in
  expect_well_formed "accept_shared_unbound_range_hole" substitution

let test_reject_invalid_hole_id_invariant () =
  let substitution = substitution ~exps:[ (0, int_const 0) ] () in
  expect_invariant_error "reject_invalid_hole_id_invariant"
    (Sub.Invalid_hole_id 0) substitution

let test_reject_overlapping_domains_invariant () =
  let substitution =
    substitution ~exps:[ (1, int_const 1) ] ~stmt_seqs:[ (1, []) ] ()
  in
  expect_invariant_error "reject_overlapping_domains_invariant"
    (Sub.Overlapping_domains 1) substitution

let test_reject_inconsistent_sort_invariant () =
  let substitution =
    substitution ~exps:[ (1, S.ExpHole 3) ]
      ~stmt_seqs:[ (2, [ S.StmtSeqHole 3 ]) ] ()
  in
  expect_invariant_error "reject_inconsistent_sort_invariant"
    (Sub.Inconsistent_hole_sort 3) substitution

let test_reject_non_idempotent_exp_invariant () =
  let substitution =
    substitution ~exps:[ (1, S.ExpHole 2); (2, int_const 2) ] ()
  in
  expect_invariant_error "reject_non_idempotent_exp_invariant"
    (Sub.Non_idempotent { hole = 2; sort = Sub.Exp })
    substitution

let test_reject_non_idempotent_stmt_seq_invariant () =
  let substitution =
    substitution
      ~stmt_seqs:[ (1, [ S.StmtSeqHole 2 ]); (2, []) ] ()
  in
  expect_invariant_error "reject_non_idempotent_stmt_seq_invariant"
    (Sub.Non_idempotent { hole = 2; sort = Sub.StmtSeq })
    substitution

let test_apply_is_idempotent () =
  let substitution =
    expect_ok "bind H1" (Sub.bind_exp Sub.empty 1 (S.ExpHole 2))
    |> fun substitution ->
    expect_ok "bind H2" (Sub.bind_exp substitution 2 (int_const 10))
  in
  let input = plus (S.ExpHole 1) (S.ExpHole 2) in
  let once = Sub.apply_exp substitution input in
  let twice = Sub.apply_exp substitution once in
  expect_exp "apply_is_idempotent" once twice;
  expect_well_formed "apply_is_idempotent" substitution

let test_string_of_t_is_sorted () =
  let substitution =
    substitution ~exps:[ (2, int_const 2); (1, int_const 1) ] ()
  in
  let actual = Sub.string_of_t substitution in
  let expected = "{ exps = [H1 -> 1; H2 -> 2]; stmt_seqs = [] }" in
  if actual <> expected then
    failwith
      (Printf.sprintf "string_of_t_is_sorted: expected %S, got %S" expected
         actual)

let () =
  let cases =
    [
      ("apply_exp_nested", test_apply_exp_nested);
      ("apply_stmt_seq_splices_tail", test_apply_stmt_seq_splices_tail);
      ("apply_nested_block", test_apply_nested_block);
      ("apply_ast", test_apply_ast);
      ("bind_normalizes_new_rhs", test_bind_normalizes_new_rhs);
      ("bind_updates_old_rhs", test_bind_updates_old_rhs);
      ("exp_bind_updates_stmt_seq_rhs", test_exp_bind_updates_stmt_seq_rhs);
      ("stmt_seq_bind_updates_old_rhs", test_stmt_seq_bind_updates_old_rhs);
      ("reject_direct_exp_occurs", test_reject_direct_exp_occurs);
      ("reject_indirect_exp_occurs", test_reject_indirect_exp_occurs);
      ("reject_direct_stmt_seq_occurs", test_reject_direct_stmt_seq_occurs);
      ("reject_indirect_stmt_seq_occurs", test_reject_indirect_stmt_seq_occurs);
      ("reject_already_bound", test_reject_already_bound);
      ("reject_sort_mismatch", test_reject_sort_mismatch);
      ( "reject_inconsistent_domains_on_bind",
        test_reject_inconsistent_domains_on_bind );
      ("fold_bind", test_fold_bind);
      ("compose_direction", test_compose_direction);
      ("compose_exp_into_stmt_seq", test_compose_exp_into_stmt_seq);
      ( "compose_rejects_overlapping_domain",
        test_compose_rejects_overlapping_domain );
      ( "accept_shared_unbound_range_hole",
        test_accept_shared_unbound_range_hole );
      ("reject_invalid_hole_id_invariant", test_reject_invalid_hole_id_invariant);
      ( "reject_overlapping_domains_invariant",
        test_reject_overlapping_domains_invariant );
      ( "reject_inconsistent_sort_invariant",
        test_reject_inconsistent_sort_invariant );
      ( "reject_non_idempotent_exp_invariant",
        test_reject_non_idempotent_exp_invariant );
      ( "reject_non_idempotent_stmt_seq_invariant",
        test_reject_non_idempotent_stmt_seq_invariant );
      ("apply_is_idempotent", test_apply_is_idempotent);
      ("string_of_t_is_sorted", test_string_of_t_is_sorted);
    ]
  in
  List.iter
    (fun (name, run) ->
      run ();
      Printf.printf "ok - %s\n" name)
    cases
