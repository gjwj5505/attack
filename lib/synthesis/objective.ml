open Language

type witness = {
  cval : int;
  aval : Analyzer.Abs_domain.Abs_val.t;
  reason : string;
}

type t = {
  name : string;
  check :
    cfg:Config.t ->
    var:string ->
    tree:BigStep.ctree ->
    cmd:Syntax.Cmd.t ->
    analysis_aenv:Analyzer.Abs_domain.Abs_env.t ->
    witness option;
}

let string_of_witness w =
  Printf.sprintf "%s: concrete=%d abstract=%s" w.reason w.cval
    (Analyzer.Abs_domain.Abs_val.string_of_t w.aval)

let final_concrete_value var tree =
  let _, _, final_cenv = BigStep.get_c_concl tree in
  Environment.lookup var final_cenv

let abstract_value var analysis_aenv =
  Analyzer.Abs_domain.Abs_env.find var analysis_aenv

let singleton cval = Analyzer.Itv.singleton cval

let contains_concrete cval aval =
  Analyzer.Itv.(singleton cval <= aval)

let is_singleton cval aval = Analyzer.Itv.equal aval (singleton cval)

let is_unbounded = function
  | Analyzer.Itv.Bot -> false
  | Analyzer.Itv.Itv (Analyzer.Itv.Bound.N_inf, _)
  | Analyzer.Itv.Itv (_, Analyzer.Itv.Bound.P_inf) ->
      true
  | Analyzer.Itv.Itv _ -> false

let make name check = { name; check }

let top =
  make "top"
    (fun ~cfg:_ ~var ~tree ~cmd:_ ~analysis_aenv ->
      let cval = final_concrete_value var tree in
      let aval = abstract_value var analysis_aenv in
      if Analyzer.Abs_domain.Abs_val.is_top aval then
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
