open Language

let src = ref ""
let opt_pp = ref false
let opt_big = ref false

let usage =
  "Usage : " ^ Filename.basename Sys.argv.(0) ^ " [-pp|-big] [c-file] "

let fail_usage msg =
  prerr_endline ("Error: " ^ msg);
  prerr_endline usage;
  exit 2

let set_src x =
  if !src <> "" then fail_usage ("unexpected extra input file: " ^ x)
  else src := x

let has_action () = !opt_pp || !opt_big

let parse_file () =
  if !src = "" then fail_usage "input file required";
  match CilBridge.parse_c_file_as_file !src with
  | Ok file -> file
  | Error err ->
      prerr_endline (CilBridge.string_of_error err);
      exit 1

let print_file file =
  match Check.check_file file with
  | Ok () -> (
      match CilBridge.write_file stdout file with
      | Ok () -> ()
      | Error err ->
          prerr_endline (CilBridge.string_of_error err);
          exit 1 )
  | Error err ->
      prerr_endline (Check.string_of_error err);
      exit 1

let run_big_step file =
  match Check.check_file file with
  | Error err ->
      prerr_endline (Check.string_of_error err);
      exit 1
  | Ok () -> (
      match Derivator.derive_file file with
      | Ok tree ->
          let BigStep.PTreeMainReturn (_, (_, _, value)) = tree in
          Printf.printf "Big-Step tree constructed. main returned %s\n"
            (Value.string_of_t value)
      | Error err ->
          prerr_endline (Derivator.string_of_error err);
          exit 1 )

let main () =
  let speclist =
    [
      ( "-pp",
        Arg.Unit (fun _ -> opt_pp := true),
        "parse C with GoblintCil, lower to CIL', convert back to CIL, and print" );
      ( "-big",
        Arg.Unit (fun _ -> opt_big := true),
        "derive and print a CIL' Big-Step tree" );
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
  if !opt_pp then print_file file;
  if !opt_big then run_big_step file

let () = main ()
