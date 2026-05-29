open Language

type witness = {
  cval : int;
  aval : Analyzer.aval;
  reason : string;
}

type t = {
  name : string;
  check :
    cfg:Config.t ->
    var:string ->
    tree:BigStep.ctree ->
    cmd:Syntax.Cmd.t ->
    analysis_aenv:Analyzer.aenv ->
    witness option;
}

let string_of_witness w =
  Printf.sprintf "concrete=%d abstract=%s" w.cval
    (Analyzer.string_of_aval w.aval)

let final_concrete_value var tree =
  let _, _, final_cenv = BigStep.get_c_concl tree in
  Environment.lookup var final_cenv

let abstract_value var analysis_aenv =
  Analyzer.find var analysis_aenv

let contains_concrete cval aval =
  Analyzer.contains_concrete cval aval

let is_singleton cval aval = Analyzer.is_singleton cval aval

let is_unbounded aval = Analyzer.is_unbounded aval

let make name check = { name; check }

let top =
  make "top"
    (fun ~cfg:_ ~var ~tree ~cmd:_ ~analysis_aenv ->
      let cval = final_concrete_value var tree in
      let aval = abstract_value var analysis_aenv in
      if Analyzer.is_top aval then
        Some { cval; aval; reason = "top" }
      else None)

let nonsingleton =
  make "nonsingleton"
    (fun ~cfg:_ ~var ~tree ~cmd:_ ~analysis_aenv ->
      let cval = final_concrete_value var tree in
      let aval = abstract_value var analysis_aenv in
      if
        contains_concrete cval aval
        && not (is_singleton cval aval)
      then
        Some { cval; aval; reason = "non-singleton" }
      else None)

let unbounded =
  make "unbounded"
    (fun ~cfg:_ ~var ~tree ~cmd:_ ~analysis_aenv ->
      let cval = final_concrete_value var tree in
      let aval = abstract_value var analysis_aenv in
      if contains_concrete cval aval && is_unbounded aval then
        Some { cval; aval; reason = "unbounded" }
      else None)

let unsound =
  make "unsound"
    (fun ~cfg:_ ~var ~tree ~cmd:_ ~analysis_aenv ->
      let cval = final_concrete_value var tree in
      let aval = abstract_value var analysis_aenv in
      if not (contains_concrete cval aval) then
        Some { cval; aval; reason = "unsound" }
      else None)

let all = [ top; nonsingleton; unbounded; unsound ]

let names () =
  all |> List.map (fun objective -> objective.name) |> String.concat "|"

let of_name name =
  all |> List.find_opt (fun objective -> objective.name = name)
