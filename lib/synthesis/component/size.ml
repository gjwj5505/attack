open Language.Syntax
open Language.Syntax.BigStep

let rec sizeof_Exp = function
  | Int _ -> 1
  | Var _ -> 1
  | Bop (_, e1, e2) -> 1 + sizeof_Exp e1 + sizeof_Exp e2
  | Uop (_, e) -> 1 + sizeof_Exp e

let rec sizeof_Cmd = function
  | Assign (_, e) -> 1 + sizeof_Exp e
  | Seq (c1, c2) -> 1 + sizeof_Cmd c1 + sizeof_Cmd c2
  | If (e, c1, c2) -> 1 + sizeof_Exp e + sizeof_Cmd c1 + sizeof_Cmd c2
  | While (e, c) -> 1 + sizeof_Exp e + sizeof_Cmd c


let rec sizeof_tree = function
  | ETree et -> sizeof_etree et
  | CTree ct -> sizeof_ctree ct

and sizeof_etree = function
  | EInt (_, (_, e, _)) -> sizeof_Exp e (* = 1 *)
  | EVar (_, (_, e, _)) -> sizeof_Exp e (* = 1 *)
  | EBop ((et1, et2), (_, e, _)) ->
      sizeof_Exp e + sizeof_etree et1 + sizeof_etree et2
  | EUop (et, (_, e, _)) ->
      sizeof_Exp e + sizeof_etree et

and sizeof_ctree = function
  | Assign (et, (_, c, _)) ->
      sizeof_Cmd c + sizeof_etree et
  | Seq ((ct1, ct2), (_, c, _)) ->
      sizeof_Cmd c + sizeof_ctree ct1 + sizeof_ctree ct2
  | IfTrue ((et, ct), (_, c, _)) ->
      sizeof_Cmd c + sizeof_etree et + sizeof_ctree ct
  | IfFalse ((et, ct), (_, c, _)) ->
      sizeof_Cmd c + sizeof_etree et + sizeof_ctree ct
  | WhileTrue ((et, body, rest), (_, c, _)) ->
      sizeof_Cmd c + sizeof_etree et + sizeof_ctree body + sizeof_ctree rest
  | WhileFalse (et, (_, c, _)) ->
      sizeof_Cmd c + sizeof_etree et