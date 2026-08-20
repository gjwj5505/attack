open Language

module S = Syntax
module B = BigStep

let int_t = Typ.TInt Typ.IInt
let mem = Memory.empty

let value n =
  match Value.of_constant (S.CInt (Int64.of_int n, Typ.IInt)) with
  | Ok value -> value
  | Error error -> failwith (Value.string_of_error error)

let assert_size label expected actual =
  if not (Size.equal expected actual) then
    failwith
      (Printf.sprintf "%s: expected %s, got %s" label
         (Size.to_string expected) (Size.to_string actual))
  else Printf.printf "ok - %s\n" label

let ground_int n : S.ground S.exp =
  S.Const (S.CInt (Int64.of_int n, Typ.IInt))

let holed_int n : S.holed S.exp =
  S.Const (S.CInt (Int64.of_int n, Typ.IInt))

let test_scalar_size () =
  assert_size "scalar_add" 5 (Size.add 2 3);
  assert_size "scalar_sub" 2 (Size.sub 5 3);
  if not (Size.is_valid 0) || Size.is_valid (-1) then
    failwith "scalar validity mismatch"
  else Printf.printf "ok - scalar_validity\n"

let test_syntax_size () =
  let left = ground_int 1 in
  let right = ground_int 2 in
  assert_size "syntax_constant" 2 (SyntaxSize.sizeof_exp left);
  assert_size "syntax_binary" 5
    (SyntaxSize.sizeof_exp (S.BinOp (S.PlusA, left, right, int_t)));
  assert_size "syntax_exp_hole" 1
    (SyntaxSize.sizeof_exp (S.ExpHole 1));
  let return_stmt : S.ground S.stmt =
    { S.labels = []; skind = S.Return (Some left); sid = None }
  in
  assert_size "syntax_block" 4
    (SyntaxSize.sizeof_block { S.bstmts = [ S.Stmt return_stmt ] });
  let tail_block : S.holed S.block =
    { S.bstmts = [ S.StmtSeqHole 2 ] }
  in
  assert_size "syntax_tail_hole_block" 2
    (SyntaxSize.sizeof_block tail_block)

let test_proof_size () =
  let left_exp = ground_int 1 in
  let right_exp = ground_int 2 in
  let left = B.ETreeConst (mem, left_exp, value 1) in
  let right = B.ETreeConst (mem, right_exp, value 2) in
  assert_size "proof_leaf" 1 (ProofSize.sizeof_etree left);
  let binary_exp = S.BinOp (S.PlusA, left_exp, right_exp, int_t) in
  let binary = B.ETreeBinOp (left, right, (mem, binary_exp, value 3)) in
  assert_size "proof_binary" 3 (ProofSize.sizeof_etree binary);
  assert_size "proof_tree_wrapper" 3
    (ProofSize.sizeof_tree (B.ETree binary));
  let holed_left_exp = holed_int 1 in
  let holed_left = B.ETreeConst (mem, holed_left_exp, value 1) in
  let short_circuit_exp =
    S.BinOp (S.LOr, holed_left_exp, S.ExpHole 3, int_t)
  in
  let short_circuit =
    B.ETreeLogicalOrLeftTrue
      (holed_left, (mem, short_circuit_exp, value 1))
  in
  assert_size "proof_holed_short_circuit" 2
    (ProofSize.sizeof_etree short_circuit);
  let large_skipped_exp =
    S.BinOp
      ( S.LOr,
        holed_left_exp,
        S.BinOp (S.PlusA, holed_int 2, holed_int 3, int_t),
        int_t )
  in
  let same_proof_shape =
    B.ETreeLogicalOrLeftTrue
      (holed_left, (mem, large_skipped_exp, value 1))
  in
  assert_size "proof_ignores_conclusion_syntax" 2
    (ProofSize.sizeof_etree same_proof_shape)

let () =
  test_scalar_size ();
  test_syntax_size ();
  test_proof_size ()
