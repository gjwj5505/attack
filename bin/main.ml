open Language

let src = ref ""
let opt_pp = ref false
(*
 * Big-Step CLI is sealed while Big-Step is ported from the old C-like AST to
 * CIL'. Keep this code here so the option can be restored deliberately later.
let opt_big = ref false
*)

let usage =
  "Usage : " ^ Filename.basename Sys.argv.(0) ^ " [-pp] [c-file] "

let fail_usage msg =
  prerr_endline ("Error: " ^ msg);
  prerr_endline usage;
  exit 2

let set_src x =
  if !src <> "" then fail_usage ("unexpected extra input file: " ^ x)
  else src := x

let has_action () = !opt_pp

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

(*
let run_big_step _file =
  prerr_endline "-big is temporarily disabled until Big-Step is ported to CIL'.";
  exit 2
*)

let main () =
  let speclist =
    [
      ( "-pp",
        Arg.Unit (fun _ -> opt_pp := true),
        "parse C with GoblintCil, lower to CIL', convert back to CIL, and print" );
(*
      ( "-big",
        Arg.Unit (fun _ -> opt_big := true),
        "derive and print a CIL' Big-Step tree" );
*)
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
    print_endline "Please provide an option. Currently useful: -pp.";
    exit 0);

  let file = parse_file () in
  if !opt_pp then print_file file
(*
  if !opt_big then run_big_step file
*)

let () = main ()
