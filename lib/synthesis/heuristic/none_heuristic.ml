open Language

type t = unit

type state = t

let make () = ()

let score_exp () (_ : Syntax.Exp.t) = 0.0

let score_cmd () (_ : Syntax.Cmd.t) = 0.0

let score_etree () (_ : BigStep.etree) = 0.0

let score_ctree () (_ : BigStep.ctree) = 0.0

let take_n n xs =
  let rec loop k xs acc =
    match (k, xs) with
    | 0, _ -> List.rev acc
    | _, [] -> List.rev acc
    | k, x :: xs -> loop (k - 1) xs (x :: acc)
  in
  loop n xs []

let choose_n (_ : t) n items = take_n n items

let trim (_ : t) items = items

let grow_count = function
  | rule when BigStep.is_ternary_grow_rule rule -> 10
  | _ -> 32

let choose_for_grow t rule items = choose_n t (grow_count rule) items
