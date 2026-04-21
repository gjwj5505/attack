open Language

let src = ref ""
let opt_pp = ref false
let opt_tab = ref false
let opt_tintp = ref false
let opt_dintp = ref false
let opt_analyze = ref false
let opt_big = ref false
let opt_attack = ref false
let bound_prog = ref 0
let bound_proof = ref 0

let usage =
  "Usage : " ^ Filename.basename Sys.argv.(0) ^ " [-option] [filename] "

let program_options () =
  !opt_pp || !opt_tab || !opt_tintp || !opt_dintp || !opt_analyze || !opt_big

let fail_usage msg =
  prerr_endline ("Error: " ^ msg);
  prerr_endline usage;
  exit 2

let set_src x =
  if !src <> "" then fail_usage ("unexpected extra input file: " ^ x)
  else src := x

let has_attack_bound () = !bound_prog <> 0 || !bound_proof <> 0

let print_attack_progress Synthesis.Attack.{ size; exps; cmds; etrees; ctrees }
    =
  Printf.printf "Trying size=%s: exp=%d cmd=%d etree=%d ctree=%d\n%!"
    (Size.to_string size) exps cmds etrees ctrees

let print_attack_result (result : Synthesis.Attack.result) =
  let labeled_cmd = Syntax.Cmd.(relabel (dummy_lbl result.cmd)) in
  Printf.printf "Attack found at size=%s\n"
    (Size.to_string result.Synthesis.Attack.size);
  print_endline "== program ==";
  print_endline (Syntax.Cmd.string_of_lbl_t labeled_cmd);
  print_endline "== analysis result ==";
  print_endline (Analyzer.Abs_mem.string_of_t result.analysis_result);
  print_endline "== proof tree ==";
  Visualizer.print_tree (CTree result.tree)

let run_synth_attack () =
  let cfg = Synthesis.Config.attack () in
  match
    Synthesis.Attack.find_top_attack ~on_progress:print_attack_progress ~var:"x"
      cfg
  with
  | None -> print_endline "No attack found"
  | Some result -> print_attack_result result

let run_synth_attack_all () =
  let cfg = Synthesis.Config.attack () in
  let bound = Size.make !bound_prog !bound_proof in
  let results =
    Synthesis.Attack.find_all_top_attacks ~on_progress:print_attack_progress
      ~var:"x" cfg bound
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

let main () =
  Arg.parse
    [
      ("-pp", Arg.Unit (fun _ -> opt_pp := true), "print a labeled program");
      ("-tab", Arg.Unit (fun _ -> opt_tab := true), "print a label table");
      ( "-tintp",
        Arg.Unit (fun _ -> opt_tintp := true),
        "D transitional interpreter" );
      ( "-dintp",
        Arg.Unit (fun _ -> opt_dintp := true),
        "D definitional interpreter" );
      ("-analyze", Arg.Unit (fun _ -> opt_analyze := true), "Attack analyzer");
      ( "-big",
        Arg.Unit (fun _ -> opt_big := true),
        "Derive, verify and print Big-Step tree" );
      ( "-attack",
        Arg.Unit (fun _ -> opt_attack := true),
        "synthesize attack programs for analyzer top result on x" );
      ( "-bound",
        Arg.Tuple [ Arg.Set_int bound_prog; Arg.Set_int bound_proof ],
        "set bounded attack search as <prog_size> <proof_size>" );
    ]
    set_src usage;

  if has_attack_bound () && not !opt_attack then
    fail_usage "-bound requires -attack";
  if !opt_attack && !src <> "" then
    fail_usage "-attack does not take an input file";
  if (not !opt_attack) && not (program_options ()) then (
    print_endline
      "Please provide an option! (-pp, -tab, -tintp, -dintp, -analyze, -big, \
       -attack)";
    exit 0);

  if !opt_attack then (
    run_attack ();
    exit 0);

  let channel = if !src = "" then stdin else open_in !src in
  let lexbuf = Lexing.from_channel channel in
  let pgm = Parser.prog Lexer.read lexbuf in
  if !src <> "" then close_in_noerr channel;

  let open Syntax.Cmd in
  if !opt_pp then string_of_lbl_t pgm |> print_endline;
  (if !opt_tab then
     tabulate pgm
     |> Lbl_map.(
          iter (fun l c ->
              string_of_key l ^ " |-> " ^ string_of_t c |> print_endline)));
  (if !opt_tintp then
     Language.Interpreter.(trans_intp pgm |> Mem.string_of_t |> print_endline));
  (if !opt_dintp then
     Language.Interpreter.(def_intp pgm |> Mem.string_of_t |> print_endline));
  (if !opt_analyze then
     Analyzer.(analysis pgm |> Abs_mem.string_of_t |> print_endline));
  if !opt_big then begin
    let tree = Derivator.derive_cmd pgm Environment.empty in
    Visualizer.print_tree (CTree tree);
    match BigStepChecker.check_ctree tree with
    | Ok ->
        print_endline "✅ Success: The Big-Step Proof Tree is valid.";
        print_endline (String.make 40 '-')
    | Error msg ->
        print_endline "❌ Error: Invalid Derivation Tree found!";
        print_endline ("Reason: " ^ msg)
  end;

  ()

let () = main ()
