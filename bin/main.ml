open Language

let src = ref ""
let opt_pp = ref false
let opt_tab = ref false
let opt_tintp = ref false
let opt_dintp = ref false
let opt_analyze = ref false
let opt_big = ref false

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
    ]
    (fun x -> src := x)
    ("Usage : " ^ Filename.basename Sys.argv.(0) ^ " [-option] [filename] ");

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
