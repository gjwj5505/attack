open BigStep

type size = {
  prog_size : int;
  proof_size : int;
}

let total s = s.prog_size + s.proof_size

let rec sizeof_Exp e =
  Syntax.Exp.(
    match e with
    | Int _ -> 1
    | Var _ -> 1
    | Bop (_, e1, e2) -> 1 + sizeof_Exp e1 + sizeof_Exp e2
    | Uop (_, e) -> 1 + sizeof_Exp e
  )

let rec sizeof_Cmd c =
  Syntax.Cmd.(
    match c with
    | Assign (_, e) -> 1 + sizeof_Exp e
    | Seq (c1, c2) -> 1 + sizeof_Cmd c1.cmd + sizeof_Cmd c2.cmd
    | If (e, c1, c2) -> 1 + sizeof_Exp e + sizeof_Cmd c1.cmd + sizeof_Cmd c2.cmd
    | While (e, c) -> 1 + sizeof_Exp e + sizeof_Cmd c.cmd
  )

let rec sizeof_proof = function
  | ETree et -> sizeof_etree et
  | CTree ct -> sizeof_ctree ct

and sizeof_etree = function
  | EInt _ -> 1
  | EVar _ -> 1
  | EBop ((et1, et2), _) -> 1 + sizeof_etree et1 + sizeof_etree et2
  | EUop (et, _) -> 1 + sizeof_etree et

and sizeof_ctree = function
  | Assign (et, _) -> 1 + sizeof_etree et
  | Seq ((ct1, ct2), _) -> 1 + sizeof_ctree ct1 + sizeof_ctree ct2
  | IfTrue ((et, ct), _) -> 1 + sizeof_etree et + sizeof_ctree ct
  | IfFalse ((et, ct), _) -> 1 + sizeof_etree et + sizeof_ctree ct
  | WhileTrue ((et, body, rest), _) ->
      1 + sizeof_etree et + sizeof_ctree body + sizeof_ctree rest
  | WhileFalse (et, _) -> 1 + sizeof_etree et

let sizeof_prog = function
  | ETree et ->
      (match et with
       | EInt (_, (_, e, _))
       | EVar (_, (_, e, _))
       | EBop (_, (_, e, _))
       | EUop (_, (_, e, _)) ->
           sizeof_Exp e)
  | CTree ct ->
      (match ct with
       | Assign (_, (_, c, _))
       | Seq (_, (_, c, _))
       | IfTrue (_, (_, c, _))
       | IfFalse (_, (_, c, _))
       | WhileTrue (_, (_, c, _))
       | WhileFalse (_, (_, c, _)) ->
           sizeof_Cmd c)

let sizeof_tree t =
  {
    prog_size = sizeof_prog t;
    proof_size = sizeof_proof t;
  }

let sizeof_etree et =
  sizeof_tree (ETree et)

let sizeof_ctree ct =
  sizeof_tree (CTree ct)