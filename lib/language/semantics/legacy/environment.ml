module VarMap = Map.Make (String)

type t = int VarMap.t

let empty = VarMap.empty
let update x cval cenv = VarMap.add x cval cenv
let lookup x cenv = try VarMap.find x cenv with Not_found -> 0

let string_of_env cenv =
  VarMap.bindings cenv
  |> List.map (fun (x, cval) -> Printf.sprintf "%s: %d" x cval)
  |> String.concat ", "
