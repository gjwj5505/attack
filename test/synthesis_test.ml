open Language
open Synthesis

let size prog proof = Size.make prog proof

let string_of_sizes sizes =
  sizes |> List.map Size.to_string |> String.concat "; "

let string_of_partition pieces =
  pieces |> List.map Size.to_string |> String.concat " + "

let string_of_partitions parts =
  parts |> List.map string_of_partition |> String.concat "\n  "

let env_of_bindings bindings =
  List.fold_left
    (fun env (x, v) -> Environment.update x v env)
    Environment.empty bindings

let string_of_envs envs =
  envs |> List.map Environment.string_of_env |> String.concat "; "

let equal_env = Environment.VarMap.equal Int.equal

let equal_envs actual expected =
  List.length actual = List.length expected
  && List.for_all2 equal_env actual expected

let string_of_exps exps =
  exps |> Component_set.ExpSet.elements
  |> List.map Syntax.Exp.string_of_t
  |> String.concat "; "

let string_of_cmds cmds =
  let cmds =
    cmds |> Component_set.CmdSet.elements
    |> List.map Syntax.Cmd.string_of_nolabel_t
  in
  if List.length cmds > 10 then String.concat "\n" cmds
  else String.concat "; " cmds

let string_of_etree = function
  | BigStep.EInt (_, (env, e, v))
  | EVar (_, (env, e, v))
  | EBop (_, (env, e, v))
  | EUop (_, (env, e, v)) ->
      Printf.sprintf "{%s} |- %s => %d" (Environment.string_of_env env)
        (Syntax.Exp.string_of_t e) v

let string_of_etrees etrees =
  etrees |> Component_set.ETreeSet.elements
  |> List.map string_of_etree
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

let test_bounded_envs () =
  let cfg =
    Config.make ~vars:[ "x"; "y" ] ~ints:[ 0 ] ~value_range:(0, 1) ()
  in
  let envs = Config.bounded_envs cfg in
  let expected =
    [
      env_of_bindings [ ("x", 0); ("y", 0) ];
      env_of_bindings [ ("x", 1); ("y", 0) ];
      env_of_bindings [ ("x", 0); ("y", 1) ];
      env_of_bindings [ ("x", 1); ("y", 1) ];
    ]
  in
  let env_with_unknown = env_of_bindings [ ("x", 0); ("z", 0) ] in
  let env_out_of_range = env_of_bindings [ ("x", 2); ("y", 0) ] in
  Printf.printf
    "Bottom_up.bounded_envs input={vars=[x;y]; value_range=(0,1)}\n  output=[%s]\n\n"
    (string_of_envs envs);
  assert_true "bounded_envs expected envs" (equal_envs envs expected);
  assert_true "valid_env accepts bounded env"
    (Config.valid_env cfg (env_of_bindings [ ("x", 1); ("y", 0) ]));
  assert_true "valid_env rejects unknown variable"
    (not (Config.valid_env cfg env_with_unknown));
  assert_true "valid_env rejects out-of-range value"
    (not (Config.valid_env cfg env_out_of_range))

let test_bottom_up_initial_components () =
  let tbl =
    Bottom_up.build_up_to
      (Config.make ~vars:[ "x"; "y" ] ~ints:[ 0; 1; 2 ]
         ~value_range:(0, 0) ())
      (size 1 0)
  in
  let exps = Component_set.exps_of_size (size 1 0) tbl in
  Printf.printf
    "Bottom_up.build_up_to input={vars=[x;y]; ints=[0;1;2]}, bound=(1,0)\n  exps at (1,0)=[%s]\n\n"
    (string_of_exps exps);
  assert_true "initial Int 0" (Component_set.ExpSet.mem (Syntax.Exp.Int 0) exps);
  assert_true "initial Int 1" (Component_set.ExpSet.mem (Syntax.Exp.Int 1) exps);
  assert_true "initial Var x" (Component_set.ExpSet.mem (Syntax.Exp.Var "x") exps)

let test_bottom_up_exp_growth () =
  let tbl =
    Bottom_up.build_up_to
      (Config.make ~vars:[ "x" ] ~ints:[ 0 ] ~value_range:(0, 0) ())
      (size 5 0)
  in
  let exps_2 = Component_set.exps_of_size (size 2 0) tbl in
  let exps_3 = Component_set.exps_of_size (size 3 0) tbl in
  let exps_4 = Component_set.exps_of_size (size 4 0) tbl in
  let exps_5 = Component_set.exps_of_size (size 5 0) tbl in
  let x = Syntax.Exp.Var "x" in
  let zero = Syntax.Exp.Int 0 in
  let neg_x = Syntax.Exp.Uop (Syntax.Exp.Uminus, x) in
  let neg_zero = Syntax.Exp.Uop (Syntax.Exp.Uminus, zero) in
  Printf.printf
    "Bottom_up.build_up_to input={vars=[x]; ints=[0]}, bound=(5,0)\n  exps at (2,0)=[%s]\n  exps at (3,0)=[%s]\n  exps at (4,0)=[%s]\n  exps at (5,0)=[%s]\n\n"
    (string_of_exps exps_2) (string_of_exps exps_3) (string_of_exps exps_4)
    (string_of_exps exps_5);
  assert_true "generated -x" (Component_set.ExpSet.mem neg_x exps_2);
  assert_true "generated -0" (Component_set.ExpSet.mem neg_zero exps_2);
  assert_true "generated --x"
    (Component_set.ExpSet.mem (Syntax.Exp.Uop (Syntax.Exp.Uminus, neg_x)) exps_3);
  assert_true "generated x < x"
    (Component_set.ExpSet.mem (Syntax.Exp.Bop (Syntax.Exp.Lt, x, x)) exps_3);
  assert_true "generated x < 0"
    (Component_set.ExpSet.mem (Syntax.Exp.Bop (Syntax.Exp.Lt, x, zero)) exps_3);
  assert_true "generated 0 < x"
    (Component_set.ExpSet.mem (Syntax.Exp.Bop (Syntax.Exp.Lt, zero, x)) exps_3);
  assert_true "generated 0 < 0"
    (Component_set.ExpSet.mem (Syntax.Exp.Bop (Syntax.Exp.Lt, zero, zero)) exps_3);
  assert_true "generated ---x"
    (Component_set.ExpSet.mem
       (Syntax.Exp.Uop
          (Syntax.Exp.Uminus, Syntax.Exp.Uop (Syntax.Exp.Uminus, neg_x)))
       exps_4);
  assert_true "generated x < -x"
    (Component_set.ExpSet.mem (Syntax.Exp.Bop (Syntax.Exp.Lt, x, neg_x)) exps_4);
  assert_true "generated -x < x"
    (Component_set.ExpSet.mem (Syntax.Exp.Bop (Syntax.Exp.Lt, neg_x, x)) exps_4);
  assert_true "generated x < (x < x)"
    (Component_set.ExpSet.mem
       (Syntax.Exp.Bop
          (Syntax.Exp.Lt, x, Syntax.Exp.Bop (Syntax.Exp.Lt, x, x)))
       exps_5);
  assert_true "generated -(x < -x)"
    (Component_set.ExpSet.mem
       (Syntax.Exp.Uop
          (Syntax.Exp.Uminus, Syntax.Exp.Bop (Syntax.Exp.Lt, x, neg_x)))
       exps_5)

let test_bottom_up_eint_growth () =
  let cfg =
    Config.make ~vars:[ "x" ] ~ints:[ 0; 1 ] ~value_range:(0, 1) ()
  in
  let tbl = Bottom_up.build_up_to cfg (size 1 1) in
  let etrees = Component_set.etrees_of_size (size 1 1) tbl in
  let env_x0 = env_of_bindings [ ("x", 0) ] in
  let env_x1 = env_of_bindings [ ("x", 1) ] in
  Printf.printf
    "Bottom_up.build_up_to input={vars=[x]; ints=[0;1]; value_range=(0,1)}, bound=(1,1)\n  EInt etrees at (1,1)=[%s]\n\n"
    (string_of_etrees etrees);
  assert_true "generated EInt 0 under x=0"
    (Component_set.ETreeSet.mem
       (BigStep.EInt ((), (env_x0, Syntax.Exp.Int 0, 0)))
       etrees);
  assert_true "generated EInt 1 under x=1"
    (Component_set.ETreeSet.mem
       (BigStep.EInt ((), (env_x1, Syntax.Exp.Int 1, 1)))
       etrees)

let test_bottom_up_evar_growth () =
  let cfg =
    Config.make ~vars:[ "x" ] ~ints:[ 0; 1 ] ~value_range:(0, 1) ()
  in
  let tbl = Bottom_up.build_up_to cfg (size 1 1) in
  let etrees = Component_set.etrees_of_size (size 1 1) tbl in
  let env_x0 = env_of_bindings [ ("x", 0) ] in
  let env_x1 = env_of_bindings [ ("x", 1) ] in
  Printf.printf
    "Bottom_up.build_up_to input={vars=[x]; ints=[0;1]; value_range=(0,1)}, bound=(1,1)\n  EVar etrees at (1,1)=[%s]\n\n"
    (string_of_etrees etrees);
  assert_true "generated EVar x under x=0"
    (Component_set.ETreeSet.mem
       (BigStep.EVar ((), (env_x0, Syntax.Exp.Var "x", 0)))
       etrees);
  assert_true "generated EVar x under x=1"
    (Component_set.ETreeSet.mem
       (BigStep.EVar ((), (env_x1, Syntax.Exp.Var "x", 1)))
       etrees)

let test_bottom_up_assign_growth () =
  let tbl =
    Bottom_up.build_up_to
      (Config.make ~vars:[ "x" ] ~ints:[ 0 ] ~value_range:(0, 0) ())
      (size 5 0)
  in
  let cmds_3 = Component_set.cmds_of_size (size 3 0) tbl in
  let cmds_4 = Component_set.cmds_of_size (size 4 0) tbl in
  let cmds_5 = Component_set.cmds_of_size (size 5 0) tbl in
  let x = Syntax.Exp.Var "x" in
  let zero = Syntax.Exp.Int 0 in
  let neg_x = Syntax.Exp.Uop (Syntax.Exp.Uminus, x) in
  Printf.printf
    "Bottom_up.build_up_to input={vars=[x]; ints=[0]}, bound=(5,0)\n  cmds at (3,0)=[%s]\n  cmds at (4,0)=[%s]\n  cmds at (5,0)=[%s]\n\n"
    (string_of_cmds cmds_3) (string_of_cmds cmds_4) (string_of_cmds cmds_5);
  assert_true "generated x := x"
    (Component_set.CmdSet.mem (Syntax.Cmd.Assign ("x", x)) cmds_3);
  assert_true "generated x := 0"
    (Component_set.CmdSet.mem (Syntax.Cmd.Assign ("x", zero)) cmds_3);
  assert_true "generated x := -x"
    (Component_set.CmdSet.mem (Syntax.Cmd.Assign ("x", neg_x)) cmds_4);
  assert_true "generated x := x < x"
    (Component_set.CmdSet.mem
       (Syntax.Cmd.Assign ("x", Syntax.Exp.Bop (Syntax.Exp.Lt, x, x)))
       cmds_5)

let lbl cmd = Syntax.Cmd.{ lbl = 0; cmd }

let test_bottom_up_seq_growth () =
  let tbl =
    Bottom_up.build_up_to
      (Config.make ~vars:[ "x" ] ~ints:[ 0 ] ~value_range:(0, 0) ())
      (size 11 0)
  in
  let cmds_7 = Component_set.cmds_of_size (size 7 0) tbl in
  let cmds_8 = Component_set.cmds_of_size (size 8 0) tbl in
  let cmds_9 = Component_set.cmds_of_size (size 9 0) tbl in
  let cmds_10 = Component_set.cmds_of_size (size 10 0) tbl in
  let cmds_11 = Component_set.cmds_of_size (size 11 0) tbl in
  let x = Syntax.Exp.Var "x" in
  let zero = Syntax.Exp.Int 0 in
  let assign_x = Syntax.Cmd.Assign ("x", x) in
  let assign_zero = Syntax.Cmd.Assign ("x", zero) in
  let assign_neg_x =
    Syntax.Cmd.Assign ("x", Syntax.Exp.Uop (Syntax.Exp.Uminus, x))
  in
  let assign_neg_neg_x =
    Syntax.Cmd.Assign
      ( "x",
        Syntax.Exp.Uop
          (Syntax.Exp.Uminus, Syntax.Exp.Uop (Syntax.Exp.Uminus, x)) )
  in
  let assign_neg_neg_neg_x =
    Syntax.Cmd.Assign
      ( "x",
        Syntax.Exp.Uop
          ( Syntax.Exp.Uminus,
            Syntax.Exp.Uop
              (Syntax.Exp.Uminus, Syntax.Exp.Uop (Syntax.Exp.Uminus, x)) ) )
  in
  let seq_assign_x_assign_x = Syntax.Cmd.Seq (lbl assign_x, lbl assign_x) in
  Printf.printf
    "Bottom_up.build_up_to input={vars=[x]; ints=[0]}, bound=(11,0)\n  cmds at (7,0)=[%s]\n  cmds at (8,0)=[%s]\n  cmds at (9,0)=[%s]\n  cmds at (10,0)=[%s]\n  cmds at (11,0)=[%s]\n\n"
    (string_of_cmds cmds_7) (string_of_cmds cmds_8) (string_of_cmds cmds_9)
    (string_of_cmds cmds_10) (string_of_cmds cmds_11);
  assert_true "generated (x := x); (x := x)"
    (Component_set.CmdSet.mem
       (Syntax.Cmd.Seq (lbl assign_x, lbl assign_x))
       cmds_7);
  assert_true "generated (x := x); (x := 0)"
    (Component_set.CmdSet.mem
       (Syntax.Cmd.Seq (lbl assign_x, lbl assign_zero))
       cmds_7);
  assert_true "generated (x := 0); (x := x)"
    (Component_set.CmdSet.mem
       (Syntax.Cmd.Seq (lbl assign_zero, lbl assign_x))
       cmds_7);
  assert_true "generated (x := x); (x := -x)"
    (Component_set.CmdSet.mem
       (Syntax.Cmd.Seq (lbl assign_x, lbl assign_neg_x))
       cmds_8);
  assert_true "generated (x := x); (x := --x)"
    (Component_set.CmdSet.mem
       (Syntax.Cmd.Seq (lbl assign_x, lbl assign_neg_neg_x))
       cmds_9);
  assert_true "generated (x := x); (x := ---x)"
    (Component_set.CmdSet.mem
       (Syntax.Cmd.Seq (lbl assign_x, lbl assign_neg_neg_neg_x))
       cmds_10);
  assert_true "generated ((x := x); (x := x)); (x := x)"
    (Component_set.CmdSet.mem
       (Syntax.Cmd.Seq (lbl seq_assign_x_assign_x, lbl assign_x))
       cmds_11)

let test_bottom_up_if_growth () =
  let tbl =
    Bottom_up.build_up_to
      (Config.make ~vars:[ "x" ] ~ints:[ 0 ] ~value_range:(0, 0) ())
      (size 8 0)
  in
  let cmds_8 = Component_set.cmds_of_size (size 8 0) tbl in
  let x = Syntax.Exp.Var "x" in
  let assign_x = Syntax.Cmd.Assign ("x", x) in
  Printf.printf
    "Bottom_up.build_up_to input={vars=[x]; ints=[0]}, bound=(8,0)\n  cmds at (8,0)=[%s]\n\n"
    (string_of_cmds cmds_8);
  assert_true "generated if x then (x := x) else (x := x)"
    (Component_set.CmdSet.mem
       (Syntax.Cmd.If (x, lbl assign_x, lbl assign_x))
       cmds_8)

let test_bottom_up_while_growth () =
  let tbl =
    Bottom_up.build_up_to
      (Config.make ~vars:[ "x" ] ~ints:[ 0 ] ~value_range:(0, 0) ())
      (size 9 0)
  in
  let cmds_9 = Component_set.cmds_of_size (size 9 0) tbl in
  let x = Syntax.Exp.Var "x" in
  let assign_x = Syntax.Cmd.Assign ("x", x) in
  let seq_assign_x_assign_x = Syntax.Cmd.Seq (lbl assign_x, lbl assign_x) in
  Printf.printf
    "Bottom_up.build_up_to input={vars=[x]; ints=[0]}, bound=(9,0)\n  cmds at (9,0)=[%s]\n\n"
    (string_of_cmds cmds_9);
  assert_true "generated while x do ((x := x); (x := x))"
    (Component_set.CmdSet.mem
       (Syntax.Cmd.While (x, lbl seq_assign_x_assign_x))
       cmds_9)

let run_all () =
  test_rectangular_up_to ();
  test_diagonal_up_to ();
  test_partition_with_constraints ();
  test_impossible_partition ();
  test_bounded_envs ();
  test_bottom_up_initial_components ();
  test_bottom_up_exp_growth ();
  test_bottom_up_eint_growth ();
  test_bottom_up_evar_growth ();
  test_bottom_up_assign_growth ();
  test_bottom_up_seq_growth ();
  test_bottom_up_if_growth ();
  test_bottom_up_while_growth ()

let selected_tests = ref []

let add_test name test =
  selected_tests := !selected_tests @ [ (name, test) ]

let usage = "Usage: synthesis_test.exe [options]"

let specs = ref []

let show_help () =
  Arg.usage !specs usage;
  exit 0

let () =
  specs :=
    [
      ("-h", Arg.Unit show_help, "show help");
      ("-all", Arg.Unit (fun () -> add_test "all" run_all), "run all tests");
      ( "-rect",
        Arg.Unit (fun () -> add_test "rect" test_rectangular_up_to),
        "test Partition.rectangular_up_to" );
      ( "-diag",
        Arg.Unit (fun () -> add_test "diag" test_diagonal_up_to),
        "test Partition.diagonal_up_to" );
      ( "-part",
        Arg.Unit (fun () -> add_test "part" test_partition_with_constraints),
        "test constrained partition generation" );
      ( "-imp",
        Arg.Unit (fun () -> add_test "imp" test_impossible_partition),
        "test impossible partition case" );
      ( "-env",
        Arg.Unit (fun () -> add_test "env" test_bounded_envs),
        "test bounded environment generation" );
      ( "-init",
        Arg.Unit (fun () -> add_test "init" test_bottom_up_initial_components),
        "test initial bottom-up components" );
      ( "-exp",
        Arg.Unit (fun () -> add_test "exp" test_bottom_up_exp_growth),
        "test bottom-up expression growth" );
      ( "-eint",
        Arg.Unit (fun () -> add_test "eint" test_bottom_up_eint_growth),
        "test bottom-up EInt proof tree growth" );
      ( "-evar",
        Arg.Unit (fun () -> add_test "evar" test_bottom_up_evar_growth),
        "test bottom-up EVar proof tree growth" );
      ( "-asgn",
        Arg.Unit (fun () -> add_test "asgn" test_bottom_up_assign_growth),
        "test bottom-up assign growth" );
      ( "-seq",
        Arg.Unit (fun () -> add_test "seq" test_bottom_up_seq_growth),
        "test bottom-up seq growth" );
      ( "-if",
        Arg.Unit (fun () -> add_test "if" test_bottom_up_if_growth),
        "test bottom-up if growth" );
      ( "-while",
        Arg.Unit (fun () -> add_test "while" test_bottom_up_while_growth),
        "test bottom-up while growth" );
    ]

let () =
  Arg.parse !specs
    (fun arg -> raise (Arg.Bad ("unexpected argument: " ^ arg)))
    usage;
  let tests = if !selected_tests = [] then [ ("all", run_all) ] else !selected_tests in
  List.iter
    (fun (name, test) ->
      Printf.printf "== %s ==\n" name;
      test ())
    tests;
  print_endline "tests passed"
