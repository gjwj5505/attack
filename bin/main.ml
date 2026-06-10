open Language

let src = ref ""
let opt_pp = ref false
let opt_tab = ref false
let opt_tintp = ref false
let opt_dintp = ref false
let opt_big = ref false
let opt_verbose = ref false

let usage =
  "Usage : " ^ Filename.basename Sys.argv.(0) ^ " [-option] [filename] "

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
  Syntax.Cmd.tabulate pgm
  |> Syntax.Cmd.Lbl_map.iter (fun l c ->
         Syntax.Cmd.string_of_key l ^ " |-> " ^ Syntax.Cmd.string_of_t c
         |> print_endline)

let run_big_step pgm =
  let tree = Derivator.derive_cmd pgm Environment.empty in
  Visualizer.print_tree ~verbose:!opt_verbose (CTree tree);
  match BigStepChecker.check_ctree tree with
  | Ok -> print_endline "Success: the Big-Step proof tree is valid."
  | Error msg -> print_endline ("Error: invalid derivation tree: " ^ msg)

let unavailable name =
  Printf.eprintf
    "%s is temporarily disabled while the project is reduced to language-only.\n"
    name;
  exit 2

let main () =
  Arg.parse
    [
      ("-pp", Arg.Unit (fun _ -> opt_pp := true), "print a labeled program");
      ("-tab", Arg.Unit (fun _ -> opt_tab := true), "print a label table");
      ( "-tintp",
        Arg.Unit (fun _ -> opt_tintp := true),
        "run the G transitional interpreter" );
      ( "-dintp",
        Arg.Unit (fun _ -> opt_dintp := true),
        "run the G definitional interpreter" );
      ( "-big",
        Arg.Unit (fun _ -> opt_big := true),
        "derive, verify, and print a Big-Step tree" );
      ( "-v",
        Arg.Unit (fun _ -> opt_verbose := true),
        "show rule names and sizes in Big-Step tree output" );
      ("-analyze", Arg.Unit (fun _ -> unavailable "-analyze"), "disabled");
      ("-attack", Arg.Unit (fun _ -> unavailable "-attack"), "disabled");
      ("-forever", Arg.Unit (fun _ -> unavailable "-forever"), "disabled");
      ( "-objective",
        Arg.String (fun _ -> unavailable "-objective"),
        "disabled" );
      ( "-bound",
        Arg.Tuple
          [
            Arg.Int (fun _ -> unavailable "-bound");
            Arg.Int (fun _ -> unavailable "-bound");
          ],
        "disabled" );
    ]
    set_src usage;

  if not (has_action ()) then (
    print_endline "Please provide an option! (-pp, -tab, -tintp, -dintp, -big)";
    exit 0);

  let pgm = parse_program () in
  if !opt_pp then Syntax.Cmd.string_of_lbl_t pgm |> print_endline;
  if !opt_tab then print_label_table pgm;
  if !opt_tintp then
    Interpreter.(trans_intp pgm |> Mem.string_of_t |> print_endline);
  if !opt_dintp then
    Interpreter.(def_intp pgm |> Mem.string_of_t |> print_endline);
  if !opt_big then run_big_step pgm

let () = main ()
