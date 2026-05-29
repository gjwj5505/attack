(*
 * SNU 4190.664A Static Program Analysis
 * Example code for how to use domain functors
 *)

open Dom

module Var = struct
  type t = string

  let compare = compare
end

module Loc = Var
module Loc_set = Basic_set (Loc)
module Loc_pow_set = Power_set_dom (Loc_set)
module Value = Product_dom (Itv) (Loc_pow_set)
module Memory = Fun_dom (Loc) (Value)
