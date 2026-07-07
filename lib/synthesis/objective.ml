open Language

type concrete_observation = {
  return_value : Value.int_value;
  (* TODO: add observable final memory bindings at normal main exit. *)
}

type analyzer_observation = {
  name : string;
  (* TODO: add abstract results for observable program state. *)
}

type witness = {
  reason : string;
  concrete : concrete_observation;
  analyzer : analyzer_observation;
}

type t = {
  name : string;
  check :
    file:Syntax.file ->
    tree:BigStep.ptree ->
    concrete:concrete_observation ->
    analyzer:analyzer_observation option ->
    witness option;
}

let concrete_of_ptree tree =
  let _, _, return_value = BigStepUtil.p_concl tree in
  match return_value with
  | Value.Int return_value -> Ok { return_value }
  | Value.Ptr _ -> Error "main returned a non-integer value"

let make name check = { name; check }

let none =
  make "none" (fun ~file:_ ~tree:_ ~concrete:_ ~analyzer:_ -> None)

let all = [ none ]

let names () =
  all |> List.map (fun objective -> objective.name) |> String.concat "|"

let of_name name =
  all |> List.find_opt (fun objective -> objective.name = name)
