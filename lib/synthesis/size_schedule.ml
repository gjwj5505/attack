open Language

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

let square_forever =
  let frontier bound =
    let sizes = ref [] in
    for proof = 1 to bound do
      sizes := Size.make bound proof :: !sizes
    done;
    for prog = 1 to bound - 1 do
      sizes := Size.make prog bound :: !sizes
    done;
    List.sort Size.compare !sizes
  in
  let rec of_list items () =
    match items with
    | [] -> Seq.Nil
    | size :: rest ->
        (* Raw syntax components are only needed for unexecuted command
           positions in proof trees. The first such demand for raw command
           size k is CWhileFalse at proof target (k + 2, 2), so emit (k,0)
           immediately before that target even under square traversal. *)
        if Size.proof_size size = 2 && Size.prog_size size >= 3 then
          Seq.Cons (Size.make (Size.prog_size size - 2) 0, fun () ->
              Seq.Cons (size, of_list rest))
        else Seq.Cons (size, of_list rest)
  in
  let rec bounds bound () =
    Seq.append (of_list (frontier bound)) (bounds (bound + 1)) ()
  in
  bounds 1
