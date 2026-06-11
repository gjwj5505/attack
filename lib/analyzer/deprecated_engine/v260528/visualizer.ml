open Language.Syntax

let display_width s =
  let rec loop width i =
    if i >= String.length s then width
    else
      let code = Char.code s.[i] in
      let next =
        if code land 0x80 = 0 then i + 1
        else if code land 0xE0 = 0xC0 then i + 2
        else if code land 0xF0 = 0xE0 then i + 3
        else if code land 0xF8 = 0xF0 then i + 4
        else i + 1
      in
      loop (width + 1) next
  in
  loop 0 0

let pad_right width s = s ^ String.make (max 0 (width - display_width s)) ' '

let string_of_analysis_sem sem pgm =
  let aenv_of_label lbl =
    sem |> Cmd.Lbl_map.find lbl |> Abs_domain.Abs_env.string_of_t
  in
  let split_program_line line =
    match String.index_opt line ':' with
    | None -> ("", "", line)
    | Some idx -> (
        let raw_label = String.sub line 0 idx |> String.trim in
        let rest =
          String.sub line (idx + 1) (String.length line - idx - 1)
        in
        match int_of_string_opt raw_label with
        | Some lbl -> (aenv_of_label lbl, raw_label, rest)
        | None -> ("", raw_label, rest))
  in
  let program_rows =
    Cmd.string_of_lbl_t pgm |> String.split_on_char '\n'
    |> List.map split_program_line
  in
  let exit_aenv =
    Analyzer_engine.exit_aenv sem |> Abs_domain.Abs_env.string_of_t
  in
  let analysis_w =
    program_rows
    |> List.fold_left
         (fun acc (analysis, _, _) -> max acc (display_width analysis))
         (display_width exit_aenv)
  in
  let label_w =
    program_rows
    |> List.fold_left
         (fun acc (_, label, _) -> max acc (display_width label))
         (display_width "exit")
  in
  let string_of_program label rest =
    Printf.sprintf "%s:%s"
      (String.make (max 0 (label_w - display_width label)) ' ' ^ label)
      rest
  in
  let lines =
    program_rows
    |> List.map (fun (analysis, label, rest) ->
           Printf.sprintf "%s  %s" (pad_right analysis_w analysis)
             (string_of_program label rest))
  in
  let exit_line =
    Printf.sprintf "%s  %s" (pad_right analysis_w exit_aenv)
      (string_of_program "exit" "")
  in
  String.concat "\n" (lines @ [ exit_line ])

let print_analysis_sem sem pgm =
  string_of_analysis_sem sem pgm |> print_endline
