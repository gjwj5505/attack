open Syntax

type cenv = Environment.t
type cval = int
type e_concl = cenv * Exp.t * cval
type c_concl = cenv * Cmd.t * cenv

type tree = ETree of etree | CTree of ctree

and etree =
  | EInt of unit * e_concl
  | EVar of unit * e_concl
  | EBop of (etree * etree) * e_concl
  | EUop of etree * e_concl

and ctree =
  | CAssign of etree * c_concl
  | CSeq of (ctree * ctree) * c_concl
  | CIfTrue of (etree * ctree) * c_concl
  | CIfFalse of (etree * ctree) * c_concl
  | CWhileTrue of (etree * ctree * ctree) * c_concl
  | CWhileFalse of etree * c_concl

type grow_rule =
  | GrowProgBop
  | GrowProgSeq
  | GrowProgIf
  | GrowProgWhile
  | GrowEInt
  | GrowEVar
  | GrowEBop
  | GrowEUop
  | GrowCAssign
  | GrowCSeq
  | GrowCIfTrue
  | GrowCIfFalse
  | GrowCWhileTrue
  | GrowCWhileFalse

type grow_rule_arity = Unary | Binary | Ternary

let arity_of_grow_rule = function
  | GrowEInt | GrowEVar | GrowEUop | GrowCAssign -> Unary
  | GrowProgBop | GrowProgSeq | GrowProgWhile | GrowEBop | GrowCSeq
  | GrowCWhileFalse ->
      Binary
  | GrowProgIf | GrowCIfTrue | GrowCIfFalse | GrowCWhileTrue -> Ternary

let is_binary_grow_rule rule =
  match arity_of_grow_rule rule with Binary -> true | _ -> false

let is_ternary_grow_rule rule =
  match arity_of_grow_rule rule with Ternary -> true | _ -> false

let get_e_concl = function
  | EInt (_, c) | EVar (_, c) | EBop (_, c) | EUop (_, c) -> c

let get_c_concl = function
  | CAssign (_, c)
  | CSeq (_, c)
  | CIfTrue (_, c)
  | CIfFalse (_, c)
  | CWhileTrue (_, c)
  | CWhileFalse (_, c) ->
      c

let get_start_cenv = function
  | ETree et ->
      let cenv, _, _ = get_e_concl et in
      cenv
  | CTree ct ->
      let cenv, _, _ = get_c_concl ct in
      cenv

let get_start_env = get_start_cenv

type result = V of cval | E of cenv

let get_result = function
  | ETree et ->
      let _, _, cval = get_e_concl et in
      V cval
  | CTree ct ->
      let _, _, cenv = get_c_concl ct in
      E cenv

let get_eval_val et =
  let _, _, cval = get_e_concl et in
  cval

let get_last_cenv ct =
  let _, _, cenv = get_c_concl ct in
  cenv

let get_last_env = get_last_cenv
