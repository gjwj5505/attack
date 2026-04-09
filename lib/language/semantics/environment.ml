module VarMap = Map.Make(String)

type t = int VarMap.t
let empty = VarMap.empty

let update x v env = VarMap.add x v env

let lookup x env =
  try VarMap.find x env
  with Not_found -> 0

let string_of_env env =
  VarMap.bindings env
  |> List.map (fun (x, v) -> Printf.sprintf "%s: %d" x v)
  |> String.concat ", "