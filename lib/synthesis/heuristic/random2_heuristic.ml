open Language

type t = { rng : Random.State.t }

type state = t

let make ~seed = { rng = Random.State.make [| seed |] }

let score t = Random.State.float t.rng 1.0

let score_exp t (_ : Syntax.Exp.t) = score t

let score_cmd t (_ : Syntax.Cmd.t) = score t

let score_etree t (_ : BigStep.etree) = score t

let score_ctree t (_ : BigStep.ctree) = score t

let max_count = 1000

let take_n n xs =
  let rec loop k xs acc =
    match (k, xs) with
    | 0, _ -> List.rev acc
    | _, [] -> List.rev acc
    | k, x :: xs -> loop (k - 1) xs (x :: acc)
  in
  loop n xs []

let choose_n (_t : t) n items =
  items
  |> List.stable_sort (fun (_, left) (_, right) -> Float.compare right left)
  |> take_n n

let trim t items = choose_n t max_count items

let grow_count = function
  | rule when BigStep.is_ternary_grow_rule rule -> 10
  | _ -> 32

let choose_for_grow t rule items = choose_n t (grow_count rule) items
