open Language

let src = ref ""
let opt_pp = ref false
let opt_big = ref false
let opt_ast = ref false
let opt_verbose = ref false

let usage =
  "Usage : " ^ Filename.basename Sys.argv.(0)
  ^ " [-pp|-big|-ast] [-v] [c-file] "

let fail_usage msg =
  prerr_endline ("Error: " ^ msg);
  prerr_endline usage;
  exit 2

let set_src x =
  if !src <> "" then fail_usage ("unexpected extra input file: " ^ x)
  else src := x

let has_action () = !opt_pp || !opt_big || !opt_ast

let parse_file () =
  if !src = "" then fail_usage "input file required";
  match CilBridge.parse_c_file_as_file !src with
  | Ok file -> file
  | Error err ->
      prerr_endline (CilBridge.string_of_error err);
      exit 1

let print_file file =
  match SyntaxChecker.check_file file with
  | Ok () -> (
      match CilBridge.write_file stdout file with
      | Ok () -> ()
      | Error err ->
          prerr_endline (CilBridge.string_of_error err);
          exit 1 )
  | Error err ->
      prerr_endline (SyntaxChecker.string_of_error err);
      exit 1

let ensure_dir path =
  if Sys.file_exists path then ()
  else Sys.mkdir path 0o755

let print_ast file =
  match SyntaxChecker.check_file file with
  | Ok () ->
      let out_dir = "dist/asts" in
      ensure_dir "dist";
      ensure_dir out_dir;
      let base = Filename.basename !src |> Filename.remove_extension in
      let svg_path = Filename.concat out_dir (base ^ ".svg") in
      SyntaxPretty.write_file_svg svg_path file;
      let size = Size.make (Size.sizeof_file file) 0 in
      Printf.printf "CIL-- AST size %s\nSVG written to %s\n"
        (Size.to_string size) svg_path
  | Error err ->
      prerr_endline (SyntaxChecker.string_of_error err);
      exit 1

let run_big_step file =
  match SyntaxChecker.check_file file with
  | Error err ->
      prerr_endline (SyntaxChecker.string_of_error err);
      exit 1
  | Ok () -> (
      match Derivator.derive_file file with
      | Ok tree ->
          begin
            match BigStepChecker.check_ptree ~use_check_file:false tree with
            | Valid -> ()
            | Invalid msg ->
                prerr_endline ("invalid Big-Step tree: " ^ msg);
                exit 1
          end;
          let BigStep.PTreeMainReturn (_, (_, _, value)) = tree in
          let size = Size.sizeof_tree (BigStep.PTree tree) in
          let out_dir = "dist/proofs" in
          ensure_dir "dist";
          ensure_dir out_dir;
          let base = Filename.basename !src |> Filename.remove_extension in
          let svg_path = Filename.concat out_dir (base ^ ".svg") in
          Visualizer.write_tree_svg ~verbose:!opt_verbose svg_path
            (BigStep.PTree tree);
          Printf.printf
            "Big-Step tree constructed and checked. main returned %s\nSize %s\nSVG written to %s\n"
            (Value.string_of_t value) (Size.to_string size) svg_path
      | Error err ->
          prerr_endline (Derivator.string_of_error err);
          exit 1 )

let main () =
  let speclist =
    [
      ( "-pp",
        Arg.Unit (fun _ -> opt_pp := true),
        "parse C with GoblintCil, lower to CIL--, convert back to CIL, and print" );
      ( "-big",
        Arg.Unit (fun _ -> opt_big := true),
        "derive and print a CIL-- Big-Step tree" );
      ( "-ast",
        Arg.Unit (fun _ -> opt_ast := true),
        "parse C with GoblintCil, lower to CIL--, check, and print the CIL-- AST" );
      ( "-v",
        Arg.Set opt_verbose,
        "show global and top-stack memory in Big-Step proof conclusions" );
    ]
  in
  let speclist =
    ( "-h",
      Arg.Unit
        (fun () ->
          Arg.usage speclist usage;
          exit 0),
      "Display this list of options" )
    :: speclist
  in
  Arg.parse speclist set_src usage;
  if not (has_action ()) then (
    print_endline "Please provide an option. Currently useful: -pp or -big.";
    exit 0);

  let file = parse_file () in
  if !opt_ast then print_ast file;
  if !opt_pp then print_file file;
  if !opt_big then run_big_step file

let () = main ()
