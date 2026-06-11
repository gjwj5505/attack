open Language
module Result = Sparrow_result

type result =
  | Alarm of string
  | NoAlarm of string
  | ParseError of string
  | AnalyzerError of string

type status =
  | Finished
  | Failed of result

type t = unit
type aval = Result.value option
type analysis_result = {
  status : status;
  stdout : string;
  stderr : string;
  json : Result.analysis option;
}
type aenv = analysis_result
type sem = aenv

let default_checks = [ "-dz" ]
let default = ()

let names () = "sparrow"
let of_name = function "sparrow" | "260417" | "260528" -> Some () | _ -> None

let read_all ic =
  let buf = Buffer.create 4096 in
  (try
     while true do
       Buffer.add_string buf (input_line ic);
       Buffer.add_char buf '\n'
     done
   with End_of_file -> ());
  Buffer.contents buf

let copy_file src dst =
  let ic = open_in_bin src in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () ->
      let oc = open_out_bin dst in
      Fun.protect
        ~finally:(fun () -> close_out_noerr oc)
        (fun () ->
          let bytes = Bytes.create 65536 in
          let rec loop () =
            match input ic bytes 0 (Bytes.length bytes) with
            | 0 -> ()
            | n ->
                output oc bytes 0 n;
                loop ()
          in
          loop ()))

let read_file path =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () -> read_all ic)

let classify_output status stdout stderr =
  let combined = stdout ^ stderr in
  match status with
  | Unix.WEXITED 0 ->
      if String.contains combined '#' && String.contains combined 'u' then
        if String.contains combined 'U' then Alarm combined else NoAlarm combined
      else if String.contains combined 'F' then NoAlarm combined
      else NoAlarm combined
  | Unix.WEXITED _ | Unix.WSIGNALED _ | Unix.WSTOPPED _ ->
      if
        String.contains combined 'P'
        || String.contains combined 'p'
        || String.contains combined 'E'
      then ParseError combined
      else AnalyzerError combined

let analyze_i_file ?(checks = default_checks) ?json_dump path =
  let cwd = Sys.getcwd () in
  let dump_args =
    match json_dump with
    | None -> []
    | Some path -> [ "-json_dump"; path ]
  in
  let args =
    String.concat " " (List.map Filename.quote (checks @ dump_args @ [ path ]))
  in
  let command =
    Printf.sprintf "docker run --rm -v %s:/work attack-sparrow %s"
      (Filename.quote cwd) args
  in
  let env = Unix.environment () in
  let stdout, stdin, stderr = Unix.open_process_full command env in
  close_out_noerr stdin;
  let out = read_all stdout in
  let err = read_all stderr in
  let process_status = Unix.close_process_full (stdout, stdin, stderr) in
  let json_text =
    match json_dump with
    | Some path when Sys.file_exists path -> Some (read_file path)
    | _ -> None
  in
  let json = Option.map Sparrow_result_json.analysis_of_string json_text in
  let stdout =
    match json_text with
    | Some text -> out ^ "\n== JSON dump ==\n" ^ text
    | None -> out
  in
  let status =
    match process_status with
    | Unix.WEXITED 0 -> Finished
    | _ -> Failed (classify_output process_status stdout err)
  in
  { status; stdout; stderr = err; json }

let analyze_file ?(checks = default_checks) path =
  let tmp = Filename.temp_file ~temp_dir:"." "attack-sparrow-" ".i" in
  let json = Filename.temp_file ~temp_dir:"." "attack-sparrow-" ".json" in
  let tmp_base = Filename.basename tmp in
  let json_base = Filename.basename json in
  Fun.protect
    ~finally:(fun () ->
      if Sys.file_exists tmp then Sys.remove tmp;
      if Sys.file_exists json then Sys.remove json)
    (fun () ->
      copy_file path tmp;
      analyze_i_file ~checks ~json_dump:json_base tmp_base)

let analyze_program_text ?(checks = default_checks) text =
  let tmp = Filename.temp_file ~temp_dir:"." "attack-sparrow-" ".i" in
  let json = Filename.temp_file ~temp_dir:"." "attack-sparrow-" ".json" in
  let tmp_base = Filename.basename tmp in
  let json_base = Filename.basename json in
  Fun.protect
    ~finally:(fun () ->
      if Sys.file_exists tmp then Sys.remove tmp;
      if Sys.file_exists json then Sys.remove json)
    (fun () ->
      let oc = open_out_bin tmp in
      Fun.protect
        ~finally:(fun () -> close_out_noerr oc)
        (fun () -> output_string oc text);
      analyze_i_file ~checks ~json_dump:json_base tmp_base)

let analysis ?(init_cenv = Environment.empty) _analyzer pgm =
  ignore init_cenv;
  Syntax.Cmd.string_of_lbl_t pgm |> analyze_program_text

let analysis_sem ?init_cenv analyzer pgm = analysis ?init_cenv analyzer pgm

let exit_aenv sem = sem

let ends_with s suffix =
  let len_s = String.length s in
  let len_suffix = String.length suffix in
  len_s >= len_suffix
  && String.sub s (len_s - len_suffix) len_suffix = suffix

let binding_matches_var var binding =
  binding.Result.loc = var || ends_with binding.Result.loc ("," ^ var ^ ")")

let find_binding_in_node var node =
  node.Result.mem.Result.bindings
  |> List.find_opt (binding_matches_var var)
  |> Option.map (fun binding -> binding.Result.value)

let find var aenv =
  match aenv.json with
  | None -> None
  | Some json ->
      let find_in_main_exit () =
        match json.Result.main_exit_node with
        | None -> None
        | Some main_exit_node ->
            Option.bind
              (json.Result.input
              |> List.find_opt (fun node -> node.Result.node = main_exit_node))
              (find_binding_in_node var)
      in
      (match find_in_main_exit () with
      | Some value -> Some value
      | None ->
          json.Result.output |> List.rev
          |> List.find_map (find_binding_in_node var))

let contains_concrete cval = function
  | Some { Result.itv = Result.Interval (lo, hi); _ } ->
      Result.bound_le lo (Result.Int cval) && Result.bound_le (Result.Int cval) hi
  | _ -> false

let is_singleton cval = function
  | Some { Result.itv = Result.Interval (Result.Int lo, Result.Int hi); _ } ->
      lo = cval && hi = cval
  | _ -> false

let is_top = function
  | Some { Result.itv = Result.Interval (Result.Neg_inf, Result.Pos_inf); _ } -> true
  | None -> true
  | _ -> false

let is_unbounded = function
  | Some { Result.itv = Result.Interval (Result.Neg_inf, _); _ }
  | Some { Result.itv = Result.Interval (_, Result.Pos_inf); _ } ->
      true
  | _ -> false

let string_of_failure = function
  | Alarm output -> "Alarm\n" ^ output
  | NoAlarm output -> "NoAlarm\n" ^ output
  | ParseError output -> "ParseError\n" ^ output
  | AnalyzerError output -> "AnalyzerError\n" ^ output

let string_of_result aenv =
  match aenv.status with
  | Finished ->
      if
        match aenv.json with
        | Some json -> json.Result.alarms.Result.unproven > 0
        | None -> false
      then
        "Alarm\n" ^ aenv.stdout
      else "NoAlarm\n" ^ aenv.stdout
  | Failed failure -> string_of_failure failure

let string_of_aval = function
  | None -> "none"
  | Some value -> Result.string_of_value value

let string_of_aenv = string_of_result

let print_analysis_sem sem _pgm = print_endline (string_of_result sem)
