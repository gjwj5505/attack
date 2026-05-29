open Language

type t = { rng : Random.State.t }

type state = t

let make ~seed = { rng = Random.State.make [| seed |] }

let score t = Random.State.float t.rng 1.0

let score_exp t (_ : Syntax.Exp.t) = score t

let score_cmd t (_ : Syntax.Cmd.t) = score t

let score_etree t (_ : BigStep.etree) = score t

let score_ctree t (_ : BigStep.ctree) = score t

let select_some (t : t) items =
  items
  |> List.map (fun (item, score) ->
       (Random.State.float t.rng 1.0, item, score))
  |> List.stable_sort (fun (left, _, _) (right, _, _) ->
       Float.compare right left)
  |> List.map (fun (_, item, score) -> (item, score))
