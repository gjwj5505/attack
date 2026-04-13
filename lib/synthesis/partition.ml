open Language

type piece = Size.size
type constraint_ = piece -> bool

let prog_component = Size.is_prog_component
let proof_component = Size.is_proof_component

let any_component s =
  Size.prog_size s >= 1 && Size.proof_size s >= 0

let exact ~prog_size ~proof_size s =
  Size.prog_size s = prog_size && Size.proof_size s = proof_size

let rectangular_up_to bound =
  let acc = ref [] in
  for prog = 0 to Size.prog_size bound do
    for proof = 0 to Size.proof_size bound do
      acc := Size.make prog proof :: !acc
    done
  done;
  List.rev !acc

let diagonal_up_to bound =
  let acc = ref [] in
  for total = 0 to Size.total bound do
    for prog = total downto 0 do
      let proof = total - prog in
      let cur = Size.make prog proof in
      if Size.compare cur bound <= 0 then acc := cur :: !acc
    done
  done;
  List.rev !acc

let partition_with_constraints (target : piece) (constraints : constraint_ list) :
    piece list list =
  let pool = rectangular_up_to target in
  let rec aux remaining pending =
    match pending with
    | [] ->
        if Size.equal remaining (Size.make 0 0) then [ [] ] else []
    | pred :: rest ->
        pool
        |> List.filter (fun piece ->
               pred piece
               && Size.prog_size piece <= Size.prog_size remaining
               && Size.proof_size piece <= Size.proof_size remaining)
        |> List.concat_map (fun piece ->
               let rest_size = Size.sub remaining piece in
               if not (Size.is_valid rest_size) then []
               else
                 aux rest_size rest
                 |> List.map (fun suffix -> piece :: suffix))
  in
  aux target constraints

let to_string pieces =
  let body = pieces |> List.map Size.to_string |> String.concat " " in
  Printf.sprintf "[%s]" body
