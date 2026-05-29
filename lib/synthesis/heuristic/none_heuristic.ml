open Language

type t = unit

type state = t

let make () = ()

let score_exp () (_ : Syntax.Exp.t) = 0.0

let score_cmd () (_ : Syntax.Cmd.t) = 0.0

let score_etree () (_ : BigStep.etree) = 0.0

let score_ctree () (_ : BigStep.ctree) = 0.0

let select_some (_ : t) items = items
