open Language
open Synthesis

let size prog proof = Size.make prog proof

let string_of_sizes sizes =
  sizes |> List.map Size.to_string |> String.concat "; "

let string_of_partition pieces =
  pieces |> List.map Size.to_string |> String.concat " + "

let string_of_partitions parts =
  parts |> List.map string_of_partition |> String.concat "\n  "

let string_of_exps exps =
  exps |> Component_set.ExpSet.elements
  |> List.map Syntax.Exp.string_of_t
  |> String.concat "; "

let assert_equal_sizes name expected actual =
  if expected <> actual then
    failwith
      (Printf.sprintf "%s: expected [%s], got [%s]" name
         (string_of_sizes expected) (string_of_sizes actual))

let assert_true name cond =
  if not cond then failwith (name ^ ": assertion failed")

let test_rectangular_up_to () =
  let actual = Partition.rectangular_up_to (size 1 3) in
  let expected =
    [
      size 0 0;
      size 0 1;
      size 0 2;
      size 0 3;
      size 1 0;
      size 1 1;
      size 1 2;
      size 1 3;
    ]
  in
  Printf.printf "Partition.rectangular_up_to input=(1,3)\n  output=[%s]\n\n"
    (string_of_sizes actual);
  assert_equal_sizes "rectangular_up_to" expected actual

let test_diagonal_up_to () =
  let actual = Partition.diagonal_up_to (size 1 3) in
  let expected =
    [
      size 0 0;
      size 1 0;
      size 0 1;
      size 2 0;
      size 1 1;
      size 0 2;
      size 3 0;
      size 2 1;
      size 1 2;
      size 0 3;
      size 4 0;
      size 3 1;
      size 2 2;
      size 1 3;
    ]
  in
  Printf.printf "Partition.diagonal_up_to input=(1,3)\n  output=[%s]\n\n"
    (string_of_sizes actual);
  assert_equal_sizes "diagonal_up_to" expected actual

let test_partition_with_constraints () =
  let parts =
    Partition.partition_with_constraints (size 3 2)
      [ Partition.proof_component; Partition.prog_component ]
  in
  Printf.printf
    "Partition.partition_with_constraints input=(3,2), constraints=[proof; prog]\n  output=\n  %s\n\n"
    (string_of_partitions parts);
  assert_true "partition_with_constraints nonempty" (parts <> []);
  List.iter
    (function
      | [ proof; prog ] ->
          assert_true "proof component" (Partition.proof_component proof);
          assert_true "prog component" (Partition.prog_component prog);
          assert_true "sum prog"
            (Size.prog_size proof + Size.prog_size prog = 3);
          assert_true "sum proof"
            (Size.proof_size proof + Size.proof_size prog = 2)
      | _ -> failwith "partition_with_constraints: expected two pieces")
    parts

let test_impossible_partition () =
  let parts =
    Partition.partition_with_constraints (size 2 0)
      [ Partition.proof_component ]
  in
  Printf.printf
    "Partition.partition_with_constraints input=(2,0), constraints=[proof]\n  output=[%s]\n\n"
    (string_of_partitions parts);
  assert_true "impossible partition" (parts = [])

let test_bottom_up_initial_components () =
  let tbl =
    Bottom_up.build_up_to
      { Bottom_up.vars = [ "x"; "y" ]; ints = [ 0; 1; 2 ] }
      (size 1 0)
  in
  let exps = Component_set.exps_of_size (size 1 0) tbl in
  Printf.printf
    "Bottom_up.build_up_to input={vars=[x]; ints=[0;1]}, bound=(1,0)\n  exps at (1,0)=[%s]\n\n"
    (string_of_exps exps);
  assert_true "initial Int 0" (Component_set.ExpSet.mem (Syntax.Exp.Int 0) exps);
  assert_true "initial Int 1" (Component_set.ExpSet.mem (Syntax.Exp.Int 1) exps);
  assert_true "initial Var x" (Component_set.ExpSet.mem (Syntax.Exp.Var "x") exps)

let () =
  test_rectangular_up_to ();
  test_diagonal_up_to ();
  test_partition_with_constraints ();
  test_impossible_partition ();
  test_bottom_up_initial_components ();
  print_endline "tests passed"
