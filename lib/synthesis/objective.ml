open Language

type witness = {
  concrete : int;
  abstract_value : Analyzer.Abs_domain.Abs_val.t;
  reason : string;
}

type t = {
  name : string;
  check :
    cfg:Config.t ->
    var:string ->
    tree:BigStep.ctree ->
    cmd:Syntax.Cmd.t ->
    analysis_result:Analyzer.Abs_domain.Abs_mem.t ->
    witness option;
}

let string_of_witness w =
  Printf.sprintf "%s: concrete=%d abstract=%s" w.reason w.concrete
    (Analyzer.Abs_domain.Abs_val.string_of_t w.abstract_value)

let final_concrete_value var tree =
  let _, _, final_env = BigStep.get_c_concl tree in
  Environment.lookup var final_env

let abstract_value var analysis_result =
  Analyzer.Abs_domain.Abs_mem.find var analysis_result

let singleton n =
  Analyzer.Itv.singleton n

let contains_concrete concrete abstract_value =
  Analyzer.Itv.(singleton concrete <= abstract_value)

let is_singleton concrete abstract_value =
  Analyzer.Itv.equal abstract_value (singleton concrete)

let is_unbounded = function
  | Analyzer.Itv.Bot -> false
  | Analyzer.Itv.Itv (Analyzer.Itv.Bound.N_inf, _)
  | Analyzer.Itv.Itv (_, Analyzer.Itv.Bound.P_inf) ->
      true
  | Analyzer.Itv.Itv _ -> false

let make name check = { name; check }

let top =
  make "top"
    (fun ~cfg:_ ~var ~tree ~cmd:_ ~analysis_result ->
      let concrete = final_concrete_value var tree in
      let abstract_value = abstract_value var analysis_result in
      if Analyzer.Abs_domain.Abs_val.is_top abstract_value then
        Some { concrete; abstract_value; reason = "top" }
      else None)

let nonsingleton =
  make "nonsingleton"
    (fun ~cfg:_ ~var ~tree ~cmd:_ ~analysis_result ->
      let concrete = final_concrete_value var tree in
      let abstract_value = abstract_value var analysis_result in
      if
        contains_concrete concrete abstract_value
        && not (is_singleton concrete abstract_value)
      then Some { concrete; abstract_value; reason = "non-singleton" }
      else None)

let unbounded =
  make "unbounded"
    (fun ~cfg:_ ~var ~tree ~cmd:_ ~analysis_result ->
      let concrete = final_concrete_value var tree in
      let abstract_value = abstract_value var analysis_result in
      if contains_concrete concrete abstract_value && is_unbounded abstract_value
      then Some { concrete; abstract_value; reason = "unbounded" }
      else None)

let unsound =
  make "unsound"
    (fun ~cfg:_ ~var ~tree ~cmd:_ ~analysis_result ->
      let concrete = final_concrete_value var tree in
      let abstract_value = abstract_value var analysis_result in
      if not (contains_concrete concrete abstract_value) then
        Some { concrete; abstract_value; reason = "unsound" }
      else None)

let all = [ top; nonsingleton; unbounded; unsound ]

let names () =
  all |> List.map (fun objective -> objective.name) |> String.concat "|"

let of_name name =
  all |> List.find_opt (fun objective -> objective.name = name)
