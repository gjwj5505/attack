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

  
let get_e_concl = function
  | EInt (_, c) | EVar (_, c) | EBop (_, c) | EUop (_, c) -> c

let get_c_concl = function
  | Assign (_, c) | Seq (_, c) | IfTrue (_, c) | IfFalse (_, c) 
  | WhileTrue (_, c) | WhileFalse (_, c) -> c

let get_start_env = function
  | ETree et -> let (env, _, _) = get_e_concl et in env
  | CTree ct -> let (env, _, _) = get_c_concl ct in env

type result = V of value | E of env

let get_result = function
  | ETree et -> let (_, _, v) = get_e_concl et in V v
  | CTree ct -> let (_, _, e) = get_c_concl ct in E e

let get_eval_val et = 
  let (_, _, v) = get_e_concl et in v

let get_last_env ct = 
  let (_, _, env) = get_c_concl ct in env
