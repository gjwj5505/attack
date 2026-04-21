open Language.Syntax

module Abs_val = Abs_domain.Abs_val
module Abs_mem = Abs_domain.Abs_mem

let rec antp_exp (m : Abs_mem.t) : Exp.t -> Abs_val.t = function
  | Int n -> Itv.singleton n
  | Var x -> Abs_mem.find x m
  | Bop (op, e1, e2) ->
      let v1 = antp_exp m e1 in
      let v2 = antp_exp m e2 in
      Itv.bop op v1 v2
  | Uop (op, e) ->
      let v = antp_exp m e in
      Itv.uop op v
