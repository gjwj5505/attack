open Language.Syntax.BigStep

let rec sizeof_tree = function
  | ETree et -> sizeof_etree et
  | CTree ct -> sizeof_ctree ct

and sizeof_etree = function
  | EInt (_, _) | EVar (_, _) -> 1
  | EBop ((e1, e2), _) -> 1 + sizeof_etree e1 + sizeof_etree e2
  | EUop (e, _) -> 1 + sizeof_etree e

and sizeof_ctree = function
  | Assign (e, _) -> 1 + sizeof_etree e
  | Seq ((c1, c2), _) -> 1 + sizeof_ctree c1 + sizeof_ctree c2
  | IfTrue ((e, c_then), (_, cmd, _)) ->
      let s_else = match cmd with If(_, _, s) -> s | _ -> failwith "Invalid syntax" in
      1 + sizeof_etree e + sizeof_ctree c_then + (Syntax.sizeof_cmd s_else)
  | IfFalse ((e, c_else), (_, cmd, _)) ->
      let s_then = match cmd with If(_, s, _) -> s | _ -> failwith "Invalid syntax" in
      1 + sizeof_etree e + sizeof_ctree c_else + (Syntax.sizeof_cmd s_then)
  | WhileTrue ((e, c_body, c_rest), _) ->
      1 + sizeof_etree e + sizeof_ctree c_body + sizeof_ctree c_rest
  | WhileFalse (e, (_, cmd, _)) ->
      let s_body = match cmd with While(_, s) -> s | _ -> failwith "Invalid syntax" in
      1 + sizeof_etree e + (Syntax.sizeof_cmd s_body)