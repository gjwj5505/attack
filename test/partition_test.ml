open Language
open Synthesis

let size prog proof = Size.make prog proof

let string_of_sizes sizes =
  sizes |> List.map Size.to_string |> String.concat "; "

let assert_equal_sizes name expected actual =
  if expected <> actual then
    failwith
      (Printf.sprintf "%s: expected [%s], got [%s]" name
         (string_of_sizes expected) (string_of_sizes actual))

let assert_true name cond =
  if not cond then failwith (name ^ ": assertion failed")

let test_diagonal_up_to () =
  let actual = Partition.diagonal_up_to (size 3 2) in
  let expected =
    [
      size 1 0;
      size 2 0;
      size 1 1;
      size 3 0;
      size 2 1;
      size 1 2;
      size 3 1;
      size 2 2;
      size 3 2;
    ]
  in
  assert_equal_sizes "diagonal_up_to" expected actual

let test_partition_with_constraints () =
  let parts =
    Partition.partition_with_constraints (size 3 2)
      [ Partition.proof_component; Partition.prog_component ]
  in
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
  assert_true "impossible partition" (parts = [])

let () =
  test_diagonal_up_to ();
  test_partition_with_constraints ();
  test_impossible_partition ();
  print_endline "partition tests passed"
