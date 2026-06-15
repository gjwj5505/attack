open Language

let src = ref ""
let opt_pp = ref false
let opt_tab = ref false
let opt_tintp = ref false
let opt_dintp = ref false
let opt_big = ref false
(*
 * Analyzer/synthesis CLI options are temporarily disabled while the project is
 * reduced to language-only for the C subset rewrite.
let opt_attack = ref false
let opt_sparrow = ref false
let sparrow_find_var = ref None
let objective_name = ref "top"
let bound_prog = ref 0
let bound_proof = ref 0
*)
(*
 * Temporarily disabled until C Big-Step / verbose tree output is restored.
let opt_verbose = ref false
*)

let usage =
  "Usage : " ^ Filename.basename Sys.argv.(0)
  ^ " [-pp] [c-subset-file] "

let fail_usage msg =
  prerr_endline ("Error: " ^ msg);
  prerr_endline usage;
  exit 2

let set_src x =
  if !src <> "" then fail_usage ("unexpected extra input file: " ^ x)
  else src := x

let has_action () =
  !opt_pp || !opt_tab || !opt_tintp || !opt_dintp || !opt_big

let parse_program () =
  let channel = if !src = "" then stdin else open_in !src in
  Fun.protect
    ~finally:(fun () -> if !src <> "" then close_in_noerr channel)
    (fun () ->
      let lexbuf = Lexing.from_channel channel in
      Parser.prog Lexer.read lexbuf)

let print_label_table pgm =
  ignore pgm;
  print_endline "-tab is temporarily disabled for the C subset AST."

let run_big_step pgm =
  ignore pgm;
  print_endline "-big is temporarily disabled until C Big-Step is implemented."

(*
 * Analyzer/synthesis entry points are kept here as disabled reference code.
 * Re-enable these after the C language layer is in place, starting with the
 * Sparrow analyzer connection.
let blue s = "\027[34m" ^ s ^ "\027[0m"

let nonzero_field name n =
  if n = 0 then None else Some (Printf.sprintf "%-5s = %d" name n)

let string_of_fields fields =
  match List.filter_map (fun x -> x) fields with
  | [] -> "empty"
  | fields -> String.concat "; " fields

let has_attack_bound () = !bound_prog <> 0 || !bound_proof <> 0

let selected_objectives () =
  match Synthesis.Objective.of_name !objective_name with
  | Some objective -> [ Synthesis.Objective.unsound; objective ]
  | None ->
      fail_usage
        ("unknown objective: " ^ !objective_name ^ " (expected "
       ^ Synthesis.Objective.names () ^ ")")

let print_attack_progress
    Synthesis.Attack.{ size; exps; cmds; etrees; ctrees; skipped_reason; _ } =
  match skipped_reason with
  | Some _ -> ()
  | None when Size.proof_size size = 0 ->
      Printf.printf "%s\n%!"
        (blue
           (Printf.sprintf "Trying raw   size = %-8s : %s"
              (Size.to_string size)
              (string_of_fields
                 [ nonzero_field "exp" exps; nonzero_field "cmd" cmds ])))
  | None ->
      Printf.printf "Trying proof size = %-8s : %s\n%!" (Size.to_string size)
        (string_of_fields
           [ nonzero_field "etree" etrees; nonzero_field "ctree" ctrees ])

let print_attack_result (result : Synthesis.Attack.result) =
  let labeled_cmd = Syntax.Cmd.(relabel (dummy_lbl result.cmd)) in
  Printf.printf "Attack found at size=%s\n"
    (Size.to_string result.Synthesis.Attack.size);
  print_endline "== objective ==";
  Printf.printf "%s: %s\n" result.objective
    (Synthesis.Objective.string_of_witness result.witness);
  print_endline "== program ==";
  print_endline (Syntax.Cmd.string_of_lbl_t labeled_cmd);
  print_endline "== analysis result ==";
  print_endline (Analyzer.string_of_aenv result.analysis_aenv);
  print_endline "== proof tree ==";
  Visualizer.print_tree ~verbose:!opt_verbose (CTree result.tree)

let run_synth_attack () =
  let cfg = Config_util.attack () in
  match
    Synthesis.Attack.find_attack ~on_progress:print_attack_progress ~var:"x"
      ~objectives:(selected_objectives ()) cfg
  with
  | None -> print_endline "No attack found"
  | Some result -> print_attack_result result

let run_synth_attack_all () =
  let cfg = Config_util.attack () in
  let bound = Size.make !bound_prog !bound_proof in
  let results =
    Synthesis.Attack.find_all_attacks ~on_progress:print_attack_progress ~var:"x"
      ~objectives:(selected_objectives ()) cfg bound
  in
  Printf.printf "Found %d attacks up to bound=%s\n"
    (List.length results) (Size.to_string bound);
  List.iteri
    (fun i result ->
      Printf.printf "\n== attack %d ==\n" (i + 1);
      print_attack_result result)
    results

let run_attack () =
  if has_attack_bound () then run_synth_attack_all () else run_synth_attack ()

let unavailable name =
  Printf.eprintf
    "%s is temporarily disabled while the project is reduced to language-only.\n"
    name;
  exit 2
*)

let main () =
  let speclist =
    [
      ( "-pp",
        Arg.Unit (fun _ -> opt_pp := true),
        "parse and print a C subset program" );
(*
      ( "-tab",
        Arg.Unit (fun _ -> opt_tab := true),
        "disabled: label tables are not ported to the C subset AST yet" );
      ( "-tintp",
        Arg.Unit (fun _ -> opt_tintp := true),
        "disabled: the C transitional interpreter is not implemented yet" );
      ( "-dintp",
        Arg.Unit (fun _ -> opt_dintp := true),
        "disabled: the C definitional interpreter is not implemented yet" );
      ( "-big",
        Arg.Unit (fun _ -> opt_big := true),
        "disabled: C Big-Step derivation is not implemented yet" );
*)
(*
      ( "-sparrow",
        Arg.Unit (fun _ -> opt_sparrow := true),
        "run Sparrow on the input file by copying it to a temporary .i file" );
      ( "-sparrow-find",
        Arg.String (fun var -> sparrow_find_var := Some var),
        "run Sparrow and print Analyzer.find for the given variable" );
      ( "-v",
        Arg.Unit (fun _ -> opt_verbose := true),
        "show rule names and sizes in Big-Step tree output" );
      ("-analyze", Arg.Unit (fun _ -> unavailable "-analyze"), "disabled");
      ( "-attack",
        Arg.Unit (fun _ -> opt_attack := true),
        "synthesize attack programs with the Sparrow analyzer wrapper" );
      ("-forever", Arg.Unit (fun _ -> unavailable "-forever"), "disabled");
      ( "-objective",
        Arg.Set_string objective_name,
        "set attack objective: " ^ Synthesis.Objective.names ()
        ^ " (unsound is always checked first)" );
      ( "-bound",
        Arg.Tuple [ Arg.Set_int bound_prog; Arg.Set_int bound_proof ],
        "set bounded attack search as <prog_size> <proof_size>" );
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

(*
  if has_attack_bound () && not !opt_attack then
    fail_usage "-bound requires -attack";
  if !opt_attack && !src <> "" then
    fail_usage "-attack does not take an input file";
*)
  if not (has_action ()) then (
    print_endline "Please provide an option. Currently useful: -pp.";
    exit 0);

(*
  if !opt_attack then (
    run_attack ();
    exit 0);

  if !opt_sparrow then (
    if !src = "" then fail_usage "-sparrow requires an input file";
    Analyzer.analyze_file !src |> Analyzer.string_of_result |> print_endline;
    exit 0);

  (match !sparrow_find_var with
  | Some var ->
      if !src = "" then fail_usage "-sparrow-find requires an input file";
      Analyzer.analyze_file !src |> Analyzer.find var |> Analyzer.string_of_aval
      |> print_endline;
      exit 0
  | None -> ());
*)

  let pgm = parse_program () in
  if !opt_pp then Syntax.string_of_program pgm |> print_endline;
  if !opt_tab then print_label_table pgm;
  if !opt_tintp then
    print_endline
      "-tintp is temporarily disabled until the C interpreter is implemented.";
  if !opt_dintp then
    print_endline
      "-dintp is temporarily disabled until the C interpreter is implemented.";
  if !opt_big then run_big_step pgm

let () = main ()
