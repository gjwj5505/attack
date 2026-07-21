(*
 * Syntax for the Sparrow-facing CIL subset. ( = CIL-- )
 *)

type id = string

module VarId = struct
  type scope =
    | Global
    | Function of id

  type t = {
    scope : scope;
    name : id;
  }

  let compare = Stdlib.compare
  let name id = id.name
  let scope id = id.scope
  let global name = { scope = Global; name }
  let local ~function_name name = { scope = Function function_name; name }
end

type varinfo = {
  (* mutable *) vtype : Typ.t; (* CIL: typ *)
  (*
  mutable vattr : attributes;
  mutable vstorage : storage;
  *)
  (* mutable *) vglob : bool;
  (* CIL-- extension. GoblintCil varinfo has no vtemp field. *)
  vtemp : bool;
  (*
  mutable vinline : bool;
  mutable vdecl : location;
  vinit : initinfo;
  *)
  (* mutable *) vid : VarId.t;
  (*
  mutable vaddrof : bool;
  mutable vreferenced : bool;
  mutable vdescr : Pretty.doc;
  mutable vdescrpure : bool;
  mutable vhasdeclinstruction : bool;
  *)
}

type fieldinfo = {
  (* mutable fcomp : compinfo; *)
  (* mutable *) fname : string;
  (* mutable *) ftype : Typ.t; (* CIL: typ *)
  (*
  mutable fbitfield : int option;
  mutable fattr : attributes;
  mutable floc : location;
  *)
}

type constant =
  | CInt of Int64.t * Typ.ikind (* CIL: CInt of cilint * ikind * string option *)
  (*
  | CStr of string * encoding
  | CWStr of int64 list * wstring_type
  | CChr of char
  | CReal of float * fkind * string option
  | CEnum of exp * string * enuminfo
  *)

and unop =
  | Neg
  | BNot
  | LNot

and binop =
  | PlusA
  | PlusPI
  | IndexPI
  | MinusA
  | MinusPI
  | MinusPP
  | Mult
  | Div
  | Mod
  | Shiftlt
  | Shiftrt
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

and exp =
  | Const of constant
  | Lval of lval
  (* | SizeOf of Typ.t *) (* CIL: typ *)
  (* | Real of exp *)
  (* | Imag of exp *)
  (* | SizeOfE of exp *)
  (* | SizeOfStr of string *)
  (* | AlignOf of Typ.t *) (* CIL: typ *)
  (* | AlignOfE of exp *)
  | UnOp of unop * exp * Typ.t
  | BinOp of binop * exp * exp * Typ.t
  (* | Question of exp * exp * exp * Typ.t *)
  (* | CastE of Typ.t * exp *)
  | AddrOf of lval
  (* | AddrOfLabel of stmt ref *)
  | StartOf of lval

and lval = lhost * offset

and lhost =
  | Var of varinfo
  | Mem of exp

and offset =
  | NoOffset
  | Field of fieldinfo * offset
  | Index of exp * offset

module Exp = struct
  type nonrec constant = constant =
    | CInt of Int64.t * Typ.ikind

  type nonrec unop = unop =
    | Neg
    | BNot
    | LNot

  type nonrec binop = binop =
    | PlusA
    | PlusPI
    | IndexPI
    | MinusA
    | MinusPI
    | MinusPP
    | Mult
    | Div
    | Mod
    | Shiftlt
    | Shiftrt
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

  type nonrec t = exp =
    | Const of constant
    | Lval of lval
    | UnOp of unop * exp * Typ.t
    | BinOp of binop * exp * exp * Typ.t
    (* | CastE of Typ.t * exp *)
    | AddrOf of lval
    | StartOf of lval

  let string_of_constant = function
    | CInt (n, Typ.IInt) -> Int64.to_string n
    | CInt (n, Typ.IUInt) -> Int64.to_string n ^ "U"

  let string_of_unop = function
    | Neg -> "-"
    | BNot -> "~"
    | LNot -> "!"

  let string_of_binop = function
    | PlusA -> "+"
    | PlusPI -> "+"
    | IndexPI -> "+"
    | MinusA -> "-"
    | MinusPI -> "-"
    | MinusPP -> "-"
    | Mult -> "*"
    | Div -> "/"
    | Mod -> "%"
    | Shiftlt -> "<<"
    | Shiftrt -> ">>"
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

  let rec string_of_t = function
    | Const c -> string_of_constant c
    | Lval lv -> string_of_lval lv
    | UnOp (op, e, _) ->
        Printf.sprintf "(%s%s)" (string_of_unop op) (string_of_t e)
    | BinOp (op, e1, e2, _) ->
        Printf.sprintf "(%s %s %s)" (string_of_t e1) (string_of_binop op)
          (string_of_t e2)
    | AddrOf lv -> "&" ^ string_of_lval lv
    | StartOf lv -> string_of_lval lv

  and string_of_lval (host, offset) =
    string_of_lhost host ^ string_of_offset offset

  and string_of_lhost = function
    | Var v -> VarId.name v.vid
    | Mem e -> "*" ^ string_of_t e

  and string_of_offset = function
    | NoOffset -> ""
    | Field (field, offset) -> "." ^ field.fname ^ string_of_offset offset
    | Index (e, offset) ->
        "[" ^ string_of_t e ^ "]" ^ string_of_offset offset
end

type instr =
  | Set of lval * Exp.t (* CIL: * location * location *)
  | Call of lval option * Exp.t * Exp.t list (* CIL: * location * location *)
  (*
  | VarDecl of varinfo * location
  | Asm of attributes
         * string list
         * (string option * string * lval) list
         * (string option * string * Exp.t) list
         * string list
         * location
  *)

type label =
  | Label of string (* CIL: * location * bool *)
  (*
  | Case of Exp.t * location * location
  | CaseRange of Exp.t * Exp.t * location * location
  | Default of location * location
  *)

type block = {
  (* mutable battrs : attributes; *)
  bstmts : stmt list;
}

and stmt = {
  (* mutable *) labels : label list;
  (* mutable *) skind : stmtkind;
  (* mutable *) sid : int option;
  (*
  mutable succs : stmt list;
  mutable preds : stmt list;
  mutable fallthrough : stmt option;
  *)
}

and stmtkind =
  | Instr of instr list
  | Return of Exp.t option (* CIL: * location * location *)
  (* | Goto of stmt ref * location *)
  (* | ComputedGoto of Exp.t * location *)
  | If of Exp.t * block * block (* CIL: * location * location *)
  (* | Switch of Exp.t * block * stmt list * location * location *)
  | Loop of block (* CIL: * location * location * stmt option * stmt option *)
  | Break (* CIL: of location *)
  | Continue (* CIL: of location *)
  | Block of block

type fundec = {
  (* mutable *) svar : varinfo;
  (* mutable *) sformals : varinfo list;
  (* mutable *) slocals : varinfo list;
  (* mutable *) sbody : block;
  (*
  mutable smaxid : int;
  mutable smaxstmtid : int option;
  mutable sallstmts : stmt list;
  *)
}

type init =
  | SingleInit of Exp.t
  | CompoundInit of Typ.t * (offset * init) list

type initinfo = {
  init : init option; (* CIL: mutable init : init option *)
}

type global =
  (*
  | GType of typeinfo * location
  | GCompTag of compinfo * location
  | GCompTagDecl of compinfo * location
  | GEnumTag of enuminfo * location
  | GEnumTagDecl of enuminfo * location
  *)
  | GFun of fundec (* CIL: * location *)
  | GVarDecl of varinfo (* CIL: * location *)
  | GVar of varinfo * initinfo (* CIL: * location *)
  (*
  | GAsm of string * location
  | GPragma of attribute * location
  | GText of string
  *)

type file = {
  (* mutable *) fileName : string;
  (* mutable *) globals : global list;
  (*
  mutable globinit : fundec option;
  mutable globinitcalled : bool;
  *)
}

type ast =
  | AExp of exp
  | ALval of lval
  | AOffset of offset
  | AInstr of instr
  | AStmt of stmt
  | ABlock of block
  | AFundec of fundec
  | AInit of init
  | AGlobal of global
  | AFile of file

let indent lvl = String.make (2 * lvl) ' '

let string_of_varinfo v =
  Printf.sprintf "%s %s" (Typ.string_of_t v.vtype) (VarId.name v.vid)

let string_of_lval = Exp.string_of_lval

let string_of_instr = function
  | Set (lv, e) ->
      Printf.sprintf "%s = %s;" (string_of_lval lv) (Exp.string_of_t e)
  | Call (ret, f, args) ->
      let ret =
        match ret with
        | None -> ""
        | Some lv -> string_of_lval lv ^ " = "
      in
      let args = args |> List.map Exp.string_of_t |> String.concat ", " in
      Printf.sprintf "%s%s(%s);" ret (Exp.string_of_t f) args

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
  let return_type =
    match f.svar.vtype with
    | Typ.TFun (return_type, _) -> return_type
    | _ -> invalid_arg "function svar must have a function type"
  in
  let params = String.concat ", " (List.map string_of_varinfo f.sformals) in
  Printf.sprintf "%s %s(%s) %s" (Typ.string_of_t return_type)
    (VarId.name f.svar.vid) params (string_of_block f.sbody)

let rec string_of_init = function
  | SingleInit e -> Exp.string_of_t e
  | CompoundInit (_, fields) ->
      fields
      |> List.map (fun (_, init) -> string_of_init init)
      |> String.concat ", "
      |> Printf.sprintf "{ %s }"

let string_of_global = function
  | GFun f -> string_of_fundec f
  | GVarDecl v -> string_of_varinfo v ^ ";"
  | GVar (v, { init = None }) -> string_of_varinfo v ^ ";"
  | GVar (v, { init = Some init }) ->
      Printf.sprintf "%s = %s;" (string_of_varinfo v) (string_of_init init)

let string_of_file file =
  file.globals |> List.map string_of_global |> String.concat "\n\n"
