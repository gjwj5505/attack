open Language

type t = { rng : Random.State.t }

type state = t

let make ~seed = { rng = Random.State.make [| seed |] }

let score t = Random.State.float t.rng 1.0

let score_exp t (_ : Syntax.Exp.t) = score t

let score_cmd t (_ : Syntax.Cmd.t) = score t

let score_etree t (_ : BigStep.etree) = score t

let score_ctree t (_ : BigStep.ctree) = score t

let select_top_by_score ~limit ~score items =
  if limit <= 0 then []
  else
    items
    |> List.sort (fun left right ->
           let by_score = Float.compare (score right) (score left) in
           if by_score <> 0 then by_score else Stdlib.compare left right)
    |> List.to_seq |> Seq.take limit |> List.of_seq
