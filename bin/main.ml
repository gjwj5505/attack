open Language

let src = ref ""
let opt_pp = ref false
let opt_tab = ref false
let opt_tintp = ref false
let opt_dintp = ref false
let opt_analyze = ref false
let opt_big = ref false
let opt_synth_attack = ref false
let synth_bound_prog = ref 8
let synth_bound_proof = ref 6
let synth_attack_var = ref "x"

let run_synth_attack () =
  let cfg =
    Synthesis.Config.make ~vars:[ "x" ] ~ints:[ 0; 1 ] ~value_range:(0, 1) ()
  in
  let bound = Size.make !synth_bound_prog !synth_bound_proof in
  match Synthesis.Attack.find_top_attack ~var:!synth_attack_var cfg bound with
  | None ->
      Printf.printf "No attack found up to bound=%s for var=%s\n"
        (Size.to_string bound) !synth_attack_var
  | Some result ->
      Printf.printf "Attack found at size=%s for var=%s\n"
        (Size.to_string result.Synthesis.Attack.size)
        !synth_attack_var;
      print_endline "== program ==";
      print_endline (Syntax.Cmd.string_of_t result.cmd);
      print_endline "== analysis result ==";
      print_endline (Analyzer.Abs_mem.string_of_t result.analysis_result);
      print_endline "== proof tree ==";
      Visualizer.print_tree (CTree result.tree)

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
      ( "-synth-attack",
        Arg.Unit (fun _ -> opt_synth_attack := true),
        "synthesize a program whose analyzer result for a variable is top" );
      ( "-synth-bound",
        Arg.Tuple [ Arg.Set_int synth_bound_prog; Arg.Set_int synth_bound_proof ],
        "set synthesis attack bound as <prog_size> <proof_size>" );
      ( "-synth-var",
        Arg.Set_string synth_attack_var,
        "set synthesis attack target variable" );
    ]
    (fun x -> src := x)
    ("Usage : " ^ Filename.basename Sys.argv.(0) ^ " [-option] [filename] ");

  if !opt_synth_attack then (
    run_synth_attack ();
    exit 0);

  let lexbuf =
    Lexing.from_channel (if !src = "" then stdin else open_in !src)
  in
  let pgm = Parser.prog Lexer.read lexbuf in

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

  if not (!opt_pp || !opt_tab || !opt_tintp || !opt_dintp || !opt_analyze) then
    print_endline "Please provide an option! (-pp, -tab, -intp, -analyze)"

let () = main ()
