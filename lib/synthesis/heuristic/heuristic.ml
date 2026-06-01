open Language

module type HEURISTIC = sig
  type state

  val score_exp : state -> Syntax.Exp.t -> float
  val score_cmd : state -> Syntax.Cmd.t -> float
  val score_etree : state -> BigStep.etree -> float
  val score_ctree : state -> BigStep.ctree -> float
  val choose_n : state -> int -> ('a * float) list -> ('a * float) list
  val trim : state -> ('a * float) list -> ('a * float) list
  val choose_for_grow :
    state -> BigStep.grow_rule -> ('a * float) list -> ('a * float) list
end

type t = Pack : (module HEURISTIC with type state = 's) * 's -> t

let none = Pack ((module None_heuristic), None_heuristic.make ())

let random1 ~seed =
  Pack ((module Random1_heuristic), Random1_heuristic.make ~seed)

let random2 ~seed =
  Pack ((module Random2_heuristic), Random2_heuristic.make ~seed)

let my ~seed = Pack ((module My_heuristic), My_heuristic.make ~seed)

let current = ref none

let set heuristic = current := heuristic

let names () = "none|random1|random2|my"

let of_name ~seed = function
  | "none" -> Some none
  | "random1" -> Some (random1 ~seed)
  | "random2" -> Some (random2 ~seed)
  | "my" -> Some (my ~seed)
  | _ -> None

let score_exp (Pack ((module H), state)) exp = H.score_exp state exp

let score_cmd (Pack ((module H), state)) cmd = H.score_cmd state cmd

let score_etree (Pack ((module H), state)) etree = H.score_etree state etree

let score_ctree (Pack ((module H), state)) ctree = H.score_ctree state ctree

let choose_n (Pack ((module H), state)) n items = H.choose_n state n items

let trim (Pack ((module H), state)) items = H.trim state items

let choose_for_grow (Pack ((module H), state)) rule items =
  H.choose_for_grow state rule items

let score_current_exp exp = score_exp !current exp

let score_current_cmd cmd = score_cmd !current cmd

let score_current_etree etree = score_etree !current etree

let score_current_ctree ctree = score_ctree !current ctree

let choose_current_n n (items : ('a * float) list) : ('a * float) list =
  choose_n !current n items

let trim_current (items : ('a * float) list) : ('a * float) list =
  trim !current items

let choose_current_for_grow rule (items : ('a * float) list) :
    ('a * float) list =
  choose_for_grow !current rule items
