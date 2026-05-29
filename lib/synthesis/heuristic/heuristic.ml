open Language

module type HEURISTIC = sig
  type state

  val score_exp : state -> Syntax.Exp.t -> float
  val score_cmd : state -> Syntax.Cmd.t -> float
  val score_etree : state -> BigStep.etree -> float
  val score_ctree : state -> BigStep.ctree -> float
  val select_top_by_score : limit:int -> score:('a -> float) -> 'a list -> 'a list
end

type t = Pack : (module HEURISTIC with type state = 's) * 's -> t

let none = Pack ((module None_heuristic), None_heuristic.make ())

let random1 ~seed =
  Pack ((module Random1_heuristic), Random1_heuristic.make ~seed)

let random2 ~seed =
  Pack ((module Random2_heuristic), Random2_heuristic.make ~seed)

let current = ref none

let set heuristic = current := heuristic

let names () = "none|random1|random2"

let of_name ~seed = function
  | "none" -> Some none
  | "random1" -> Some (random1 ~seed)
  | "random2" -> Some (random2 ~seed)
  | _ -> None

let score_exp (Pack ((module H), state)) exp = H.score_exp state exp

let score_cmd (Pack ((module H), state)) cmd = H.score_cmd state cmd

let score_etree (Pack ((module H), state)) etree = H.score_etree state etree

let score_ctree (Pack ((module H), state)) ctree = H.score_ctree state ctree

let select_top_by_score (Pack ((module H), _)) ~limit ~score items =
  H.select_top_by_score ~limit ~score items

let score_current_exp exp = score_exp !current exp

let score_current_cmd cmd = score_cmd !current cmd

let score_current_etree etree = score_etree !current etree

let score_current_ctree ctree = score_ctree !current ctree

let select_current_top_by_score ~limit ~score items =
  select_top_by_score !current ~limit ~score items
