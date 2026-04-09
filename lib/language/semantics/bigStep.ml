open Environment
open Syntax

type env = Environment.t
type value = int

type e_concl = env * Exp.t * value
type c_concl = env * Cmd.t * env


type tree =
  | ETree of etree
  | CTree of ctree

and etree =
  | EInt   of unit * e_concl
  | EVar   of unit * e_concl
  | EBop   of (etree * etree) * e_concl
  | EUop   of etree * e_concl

and ctree =
  | Assign of etree * c_concl
  | Seq    of (ctree * ctree) * c_concl
  | IfTrue of (etree * ctree) * c_concl
  | IfFalse of (etree * ctree) * c_concl
  | WhileTrue of (etree * ctree * ctree) * c_concl
  | WhileFalse of etree * c_concl

  
let get_start_env = function
  | ETree (EInt (_, (env, _, _)))   | ETree (EVar (_, (env, _, _)))
  | ETree (EBop (_, (env, _, _)))   | ETree (EUop (_, (env, _, _)))
  | CTree (Assign (_, (env, _, _))) | CTree (Seq (_, (env, _, _)))
  | CTree (IfTrue (_, (env, _, _))) | CTree (IfFalse (_, (env, _, _)))
  | CTree (WhileTrue (_, (env, _, _))) | CTree (WhileFalse (_, (env, _, _))) -> env

type result = V of value | E of env

let get_result = function
  | ETree (EInt (_, (_, _, v)))   | ETree (EVar (_, (_, _, v)))
  | ETree (EBop (_, (_, _, v)))   | ETree (EUop (_, (_, _, v))) -> V v
  | CTree (Assign (_, (_, _, e))) | CTree (Seq (_, (_, _, e)))
  | CTree (IfTrue (_, (_, _, e))) | CTree (IfFalse (_, (_, _, e)))
  | CTree (WhileTrue (_, (_, _, e))) | CTree (WhileFalse (_, (_, _, e))) -> E e

let get_eval_val = function
  | EInt (_, (_, _, v))
  | EVar (_, (_, _, v))
  | EBop (_, (_, _, v))
  | EUop (_, (_, _, v)) -> v

let get_last_env = function
  | Assign (_, (_, _, env'))
  | Seq (_, (_, _, env'))
  | IfTrue (_, (_, _, env'))
  | IfFalse (_, (_, _, env'))
  | WhileTrue (_, (_, _, env'))
  | WhileFalse (_, (_, _, env')) -> env'