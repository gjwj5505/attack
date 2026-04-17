open Language

type piece = Size.size
type constraint_ = piece -> bool

let prog_component = Size.is_prog_component
let proof_component = Size.is_proof_component
let any_component s = Size.prog_size s >= 1 && Size.proof_size s >= 0

let exact ~prog_size ~proof_size s =
  Size.prog_size s = prog_size && Size.proof_size s = proof_size

let rectangular_up_to bound =
  let acc = ref [] in
  for prog = 1 to Size.prog_size bound do
    for proof = 0 to Size.proof_size bound do
      acc := Size.make prog proof :: !acc
    done
  done;
  List.rev !acc

let diagonal_up_to bound =
  let acc = ref [] in
  for total = 1 to Size.total bound do
    for prog = total downto 1 do
      let proof = total - prog in
      let cur = Size.make prog proof in
      if Size.compare cur bound <= 0 then acc := cur :: !acc
    done
  done;
  List.rev !acc

let partition_with_constraints (target : piece) (constraints : constraint_ list)
    : piece list list =
  let pool = rectangular_up_to target in
  let rec aux remaining pending =
    match pending with
    | [] -> if Size.equal remaining (Size.make 0 0) then [ [] ] else []
    | pred :: rest ->
        pool
        |> List.filter (fun piece ->
            pred piece
            && Size.prog_size piece <= Size.prog_size remaining
            && Size.proof_size piece <= Size.proof_size remaining)
        |> List.concat_map (fun piece ->
            let rest_size = Size.sub remaining piece in
            if not (Size.is_valid rest_size) then []
            else aux rest_size rest |> List.map (fun suffix -> piece :: suffix))
  in
  aux target constraints

let partition_special_while (target : piece)
    : piece list list =
  let acc = ref [] in
  let prog_sz = target.prog_size in
  let proof_sz = target.proof_size in
  for exp_sz = 1 to prog_sz - 3 do
    for et_sz = 1 to proof_sz - 3 do
      for c_inner_sz = 1 to proof_sz - et_sz - 2 do
        acc := [ Size.make exp_sz et_sz; 
                 Size.make (prog_sz - exp_sz - 1) c_inner_sz; 
                 Size.make prog_sz (proof_sz - et_sz - c_inner_sz - 1) ] :: !acc
      done
    done
  done;
  List.rev !acc
  

let to_string pieces =
  let body = pieces |> List.map Size.to_string |> String.concat " " in
  Printf.sprintf "[%s]" body
