open Language

let src = ref ""
let opt_pp = ref false
let opt_tab = ref false
let opt_tintp = ref false
let opt_dintp = ref false
let opt_analyze = ref false
let opt_big = ref false
let opt_attack = ref false
let opt_forever = ref false
let opt_verbose = ref false
let objective_name = ref "top"
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

let selected_objectives () =
  match Synthesis.Objective.of_name !objective_name with
  | Some objective -> [ Synthesis.Objective.unsound; objective ]
  | None ->
      fail_usage
        ("unknown objective: " ^ !objective_name ^ " (expected "
       ^ Synthesis.Objective.names () ^ ")")

let selected_heuristic () =
  let cfg = Config_util.attack () in
  match
    Synthesis.Heuristic.of_name ~seed:cfg.Config.seed cfg.Config.heuristic_name
  with
  | Some heuristic -> heuristic
  | None ->
      fail_usage
        ("unknown heuristic: " ^ cfg.Config.heuristic_name ^ " (expected "
       ^ Synthesis.Heuristic.names () ^ ")")

let selected_analyzer () =
  let cfg = Config_util.attack () in
  match Analyzer.of_name cfg.Config.analyzer_name with
  | Some analyzer -> analyzer
  | None ->
      fail_usage
        ("unknown analyzer: " ^ cfg.Config.analyzer_name ^ " (expected "
       ^ Analyzer.names () ^ ")")

let blue s =
  "\027[34m" ^ s ^ "\027[0m"

let red s =
  "\027[31m" ^ s ^ "\027[0m"

let nonzero_field name n =
  if n = 0 then None else Some (Printf.sprintf "%-5s = %d" name n)

let string_of_fields fields =
  match List.filter_map (fun x -> x) fields with
  | [] -> "empty"
  | fields -> String.concat "; " fields

let found_field n =
  if n = 0 then "" else Printf.sprintf "; found = %d" n

let print_attack_progress
    Synthesis.Attack.
      { size; exps; cmds; etrees; ctrees; found; skipped_reason } =
  match skipped_reason with
  | Some _ -> ()
  | None when Size.proof_size size = 0 ->
      Printf.printf "%s%s\n%!"
        (blue
           (Printf.sprintf "Trying raw   size = %-8s : %s"
              (Size.to_string size)
              (string_of_fields
                 [ nonzero_field "exp" exps; nonzero_field "cmd" cmds ])))
        (found_field found)
  | None ->
      Printf.printf "Trying proof size = %-8s : %s%s\n%!"
        (Size.to_string size)
        (string_of_fields
           [ nonzero_field "etree" etrees; nonzero_field "ctree" ctrees ])
        (found_field found)

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

let rec string_of_source_cmd ?(lvl = 0) (cmd : Syntax.Cmd.t) =
  let indent = String.make (2 * lvl) ' ' in
  let string_of_exp = Syntax.Exp.string_of_t in
  match cmd with
  | Assign (id, e) -> Printf.sprintf "%s%s := %s" indent id (string_of_exp e)
  | Seq (c1, c2) ->
      Printf.sprintf "%s;\n%s"
        (string_of_source_cmd ~lvl c1.Syntax.Cmd.cmd)
        (string_of_source_cmd ~lvl c2.Syntax.Cmd.cmd)
  | If (pred, con, alt) ->
      Printf.sprintf "%sif %s then\n%s\n%selse\n%s\n%send" indent
        (string_of_exp pred)
        (string_of_source_cmd ~lvl:(lvl + 1) con.Syntax.Cmd.cmd)
        indent
        (string_of_source_cmd ~lvl:(lvl + 1) alt.Syntax.Cmd.cmd)
        indent
  | While (pred, body) ->
      Printf.sprintf "%swhile %s do\n%s\n%send" indent
        (string_of_exp pred)
        (string_of_source_cmd ~lvl:(lvl + 1) body.Syntax.Cmd.cmd)
        indent

let result_path = "result.d"

let clear_attack_result_file () =
  let oc = open_out result_path in
  close_out oc

let append_attack_result_file index (result : Synthesis.Attack.result) =
  let oc =
    open_out_gen [ Open_creat; Open_text; Open_append ] 0o666 result_path
  in
  Fun.protect
    ~finally:(fun () -> close_out_noerr oc)
    (fun () ->
      Printf.fprintf oc "(* attack = %d *)\n" index;
      Printf.fprintf oc "(* size = %s; concrete = %d; abstract = %s *)\n"
        (Size.to_string result.Synthesis.Attack.size)
        result.Synthesis.Attack.witness.cval
        (Analyzer.string_of_aval
           result.Synthesis.Attack.witness.aval);
      output_string oc (string_of_source_cmd result.cmd);
      output_string oc "\n\n")

let run_synth_attack () =
  let cfg = Config_util.attack () in
  match
    Synthesis.Attack.find_attack ~on_progress:print_attack_progress
      ~heuristic:(selected_heuristic ())
      ~analyzer:(selected_analyzer ())
      ~objectives:(selected_objectives ()) cfg
  with
  | None -> print_endline "No attack found"
  | Some result -> print_attack_result result

let run_synth_attack_all () =
  let cfg = Config_util.attack () in
  let bound = Size.make !bound_prog !bound_proof in
  let results =
    Synthesis.Attack.find_all_attacks ~on_progress:print_attack_progress
      ~heuristic:(selected_heuristic ())
      ~analyzer:(selected_analyzer ())
      ~objectives:(selected_objectives ()) cfg bound
  in
  Printf.printf "Found %d attacks up to bound=%s\n"
    (List.length results) (Size.to_string bound);
  List.iteri
    (fun i result ->
      Printf.printf "\n== attack %d ==\n" (i + 1);
      print_attack_result result)
    results

let run_synth_attack_forever () =
  let cfg = Config_util.attack () in
  let attack_count = ref 0 in
  clear_attack_result_file ();
  Synthesis.Attack.iter_attacks ~on_progress:print_attack_progress
    ~heuristic:(selected_heuristic ())
    ~analyzer:(selected_analyzer ())
    ~objectives:(selected_objectives ()) cfg
    ~on_results:(fun results ->
      List.iter
        (fun result ->
          incr attack_count;
          append_attack_result_file !attack_count result)
        results;
      match results with
      | [] -> ()
      | _ ->
          Printf.printf "%s\n%!"
            (red (Printf.sprintf "found = %d" (List.length results))))

let run_attack () =
  if !opt_forever then run_synth_attack_forever ()
  else if has_attack_bound () then run_synth_attack_all ()
  else run_synth_attack ()

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
      ( "-v",
        Arg.Unit (fun _ -> opt_verbose := true),
        "show rule names and sizes in Big-Step tree output" );
      ( "-attack",
        Arg.Unit (fun _ -> opt_attack := true),
        "synthesize attack programs for analyzer objective on x" );
      ( "-forever",
        Arg.Unit (fun _ -> opt_forever := true),
        "keep synthesizing attacks and write the latest result to result.d" );
      ( "-objective",
        Arg.Set_string objective_name,
        "set attack objective: " ^ Synthesis.Objective.names ()
        ^ " (unsound is always checked first)" );
      ( "-bound",
        Arg.Tuple [ Arg.Set_int bound_prog; Arg.Set_int bound_proof ],
        "set bounded attack search as <prog_size> <proof_size>" );
    ]
    set_src usage;

  if has_attack_bound () && not !opt_attack then
    fail_usage "-bound requires -attack";
  if !opt_forever && not !opt_attack then
    fail_usage "-forever requires -attack";
  if !opt_forever && has_attack_bound () then
    fail_usage "-forever cannot be used with -bound";
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
     if !opt_verbose then
       let sem =
         Analyzer.analysis_sem (selected_analyzer ()) pgm
       in
       Analyzer.print_analysis_sem sem pgm
     else
       Analyzer.analysis (selected_analyzer ()) pgm
       |> Analyzer.string_of_aenv
       |> print_endline);
  if !opt_big then begin
    let tree = Derivator.derive_cmd pgm Environment.empty in
    Visualizer.print_tree ~verbose:!opt_verbose (CTree tree);
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
