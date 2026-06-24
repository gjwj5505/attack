(*
 * Syntax for the Sparrow-facing CIL subset.
 *)

type id = string

type varinfo = {
  vname : id;
  vtype : Typ.t;
  vglob : bool;
  vtemp : bool;
  vid : int;
}

type lval =
  | Var of varinfo

module Exp = struct
  type constant =
    | CInt64 of Int64.t

  type unop =
    | Neg
    | BNot
    | LNot

  type binop =
    | PlusA
    | MinusA
    | Mult
    | Div
    | Mod
    | Lt
    | Gt
    | Le
    | Ge
    | Eq
    | Ne
    | BAnd
    | BXor
    | BOr
    | LAnd
    | LOr
    | Shiftlt
    | Shiftrt

  type t =
    | Const of constant
    | Lval of lval
    | UnOp of unop * t * Typ.t
    | BinOp of binop * t * t * Typ.t
    | CastE of Typ.t * t

  let string_of_constant = function
    | CInt64 n -> Int64.to_string n

  let string_of_unop = function
    | Neg -> "-"
    | BNot -> "~"
    | LNot -> "!"

  let string_of_binop = function
    | PlusA -> "+"
    | MinusA -> "-"
    | Mult -> "*"
    | Div -> "/"
    | Mod -> "%"
    | Lt -> "<"
    | Gt -> ">"
    | Le -> "<="
    | Ge -> ">="
    | Eq -> "=="
    | Ne -> "!="
    | BAnd -> "&"
    | BXor -> "^"
    | BOr -> "|"
    | LAnd -> "&&"
    | LOr -> "||"
    | Shiftlt -> "<<"
    | Shiftrt -> ">>"

  let rec string_of_t = function
    | Const c -> string_of_constant c
    | Lval lv -> string_of_lval lv
    | UnOp (op, e, _) ->
        Printf.sprintf "(%s%s)" (string_of_unop op) (string_of_t e)
    | BinOp (op, e1, e2, _) ->
        Printf.sprintf "(%s %s %s)" (string_of_t e1) (string_of_binop op)
          (string_of_t e2)
    | CastE (typ, e) ->
        Printf.sprintf "((%s)%s)" (Typ.string_of_t typ) (string_of_t e)

  and string_of_lval = function
    | Var v -> v.vname
end

let string_of_lval = Exp.string_of_lval

type instr =
  | Set of lval * Exp.t

type label =
  | Label of string

type block = {
  bstmts : stmt list;
}

and stmt = {
  labels : label list;
  skind : stmtkind;
  sid : int option;
}

and stmtkind =
  | Instr of instr list
  | Return of Exp.t option
  | If of Exp.t * block * block
  | Loop of block
  | Break
  | Continue
  | Block of block

type fundec = {
  svar : varinfo;
  sformals : varinfo list;
  slocals : varinfo list;
  sbody : block;
}

type global =
  | GFun of fundec
  | GVarDecl of varinfo

type file = {
  fileName : string;
  globals : global list;
}

type program = {
  main : fundec;
}

let indent lvl = String.make (2 * lvl) ' '

let string_of_varinfo v =
  Printf.sprintf "%s %s" (Typ.string_of_t v.vtype) v.vname

let string_of_instr = function
  | Set (lv, e) ->
      Printf.sprintf "%s = %s;" (string_of_lval lv) (Exp.string_of_t e)

let string_of_label = function
  | Label name -> name ^ ":"

let rec string_of_stmt ?(lvl = 0) stmt =
  let pad = indent lvl in
  let labels =
    List.map (fun label -> pad ^ string_of_label label) stmt.labels
  in
  let body =
    match stmt.skind with
    | Instr instrs ->
        List.map (fun instr -> pad ^ string_of_instr instr) instrs
    | Return None -> [ pad ^ "return;" ]
    | Return (Some e) -> [ pad ^ "return " ^ Exp.string_of_t e ^ ";" ]
    | If (cond, tb, fb) ->
        [
          Printf.sprintf "%sif (%s) %s else %s" pad (Exp.string_of_t cond)
            (string_of_block ~lvl tb)
            (string_of_block ~lvl fb);
        ]
    | Loop body ->
        [ Printf.sprintf "%sloop %s" pad (string_of_block ~lvl body) ]
    | Break -> [ pad ^ "break;" ]
    | Continue -> [ pad ^ "continue;" ]
    | Block block -> [ pad ^ string_of_block ~lvl block ]
  in
  String.concat "\n" (labels @ body)

and string_of_block ?(lvl = 0) block =
  let inner = List.map (string_of_stmt ~lvl:(lvl + 1)) block.bstmts in
  match inner with
  | [] -> "{ }"
  | _ -> Printf.sprintf "{\n%s\n%s}" (String.concat "\n" inner) (indent lvl)

let string_of_fundec f =
  let params = String.concat ", " (List.map string_of_varinfo f.sformals) in
  Printf.sprintf "%s %s(%s) %s" (Typ.string_of_t f.svar.vtype) f.svar.vname
    params (string_of_block f.sbody)

let string_of_global = function
  | GFun f -> string_of_fundec f
  | GVarDecl v -> string_of_varinfo v ^ ";"

let string_of_file file =
  file.globals |> List.map string_of_global |> String.concat "\n\n"

let string_of_program { main } = string_of_fundec main
