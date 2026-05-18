open Language.Syntax

module Abs_val = Abs_domain.Abs_val
module Abs_env = Abs_domain.Abs_env

let rec antp_exp (aenv : Abs_env.t) : Exp.t -> Abs_val.t = function
  | Int n -> Itv.singleton n
  | Var x -> Abs_env.find x aenv
  | Bop (op, e1, e2) ->
      let aval1 = antp_exp aenv e1 in
      let aval2 = antp_exp aenv e2 in
      Itv.bop op aval1 aval2
  | Uop (op, e) ->
      let aval = antp_exp aenv e in
      Itv.uop op aval
