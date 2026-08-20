(*
 * Syntax for the Sparrow-facing CIL subset. ( = CIL-- )
 *)

type ground = Ground_mode
type holed = Holed_mode
type hole_id = int

type id = string [@@deriving eq]

module VarId = struct
  type scope =
    | Global
    | Function of id
  [@@deriving eq]

  type t = {
    scope : scope;
    name : id;
  }
  [@@deriving eq]

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
[@@deriving eq]

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
[@@deriving eq]

type constant =
  | CInt of Int64.t * Typ.ikind (* CIL: CInt of cilint * ikind * string option *)
  (*
  | CStr of string * encoding
  | CWStr of int64 list * wstring_type
  | CChr of char
  | CReal of float * fkind * string option
  | CEnum of exp * string * enuminfo
  *)
[@@deriving eq]

type unop =
  | Neg
  | BNot
  | LNot
[@@deriving eq]

type binop =
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
[@@deriving eq]

type _ exp =
  | ExpHole : hole_id -> holed exp
  | Const : constant -> 'mode exp
  | Lval : 'mode lval -> 'mode exp
  (* | SizeOf of Typ.t *) (* CIL: typ *)
  (* | Real of exp *)
  (* | Imag of exp *)
  (* | SizeOfE of exp *)
  (* | SizeOfStr of string *)
  (* | AlignOf of Typ.t *) (* CIL: typ *)
  (* | AlignOfE of exp *)
  | UnOp : unop * 'mode exp * Typ.t -> 'mode exp
  | BinOp : binop * 'mode exp * 'mode exp * Typ.t -> 'mode exp
  (* | Question of exp * exp * exp * Typ.t *)
  (* | CastE of Typ.t * exp *)
  | AddrOf : 'mode lval -> 'mode exp
  (* | AddrOfLabel of stmt ref *)
  | StartOf : 'mode lval -> 'mode exp

and 'mode lval = 'mode lhost * 'mode offset

and _ lhost =
  | Var : varinfo -> 'mode lhost
  | Mem : 'mode exp -> 'mode lhost

and _ offset =
  | NoOffset : 'mode offset
  | Field : fieldinfo * 'mode offset -> 'mode offset
  | Index : 'mode exp * 'mode offset -> 'mode offset

type 'mode instr =
  | Set of 'mode lval * 'mode exp (* CIL: * location * location *)
  | Call of 'mode lval option * 'mode exp * 'mode exp list
      (* CIL: * location * location *)
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
[@@deriving eq]

type 'mode block = {
  (* mutable battrs : attributes; *)
  bstmts : 'mode stmt_seq_item list;
}

and _ stmt_seq_item =
  | Stmt : 'mode stmt -> 'mode stmt_seq_item
  | StmtSeqHole : hole_id -> holed stmt_seq_item

and 'mode stmt = {
  (* mutable *) labels : label list;
  (* mutable *) skind : 'mode stmtkind;
  (* mutable *) sid : int option;
  (*
  mutable succs : stmt list;
  mutable preds : stmt list;
  mutable fallthrough : stmt option;
  *)
}

and 'mode stmtkind =
  | Instr of 'mode instr list
  | Return of 'mode exp option (* CIL: * location * location *)
  (* | Goto of stmt ref * location *)
  (* | ComputedGoto of Exp.t * location *)
  | If of 'mode exp * 'mode block * 'mode block
      (* CIL: * location * location *)
  (* | Switch of Exp.t * block * stmt list * location * location *)
  | Loop of 'mode block
      (* CIL: * location * location * stmt option * stmt option *)
  | Break (* CIL: of location *)
  | Continue (* CIL: of location *)
  | Block of 'mode block

type 'mode fundec = {
  (* mutable *) svar : varinfo;
  (* mutable *) sformals : varinfo list;
  (* mutable *) slocals : varinfo list;
  (* mutable *) sbody : 'mode block;
  (*
  mutable smaxid : int;
  mutable smaxstmtid : int option;
  mutable sallstmts : stmt list;
  *)
}

type 'mode init =
  | SingleInit of 'mode exp
  | CompoundInit of Typ.t * ('mode offset * 'mode init) list

type 'mode initinfo = {
  init : 'mode init option; (* CIL: mutable init : init option *)
}

type 'mode global =
  (*
  | GType of typeinfo * location
  | GCompTag of compinfo * location
  | GCompTagDecl of compinfo * location
  | GEnumTag of enuminfo * location
  | GEnumTagDecl of enuminfo * location
  *)
  | GFun of 'mode fundec (* CIL: * location *)
  | GVarDecl of varinfo (* CIL: * location *)
  | GVar of varinfo * 'mode initinfo (* CIL: * location *)
  (*
  | GAsm of string * location
  | GPragma of attribute * location
  | GText of string
  *)

type 'mode file = {
  (* mutable *) fileName : string;
  (* mutable *) globals : 'mode global list;
  (*
  mutable globinit : fundec option;
  mutable globinitcalled : bool;
  *)
}

type 'mode ast =
  | AExp of 'mode exp
  | ALval of 'mode lval
  | AOffset of 'mode offset
  | AInstr of 'mode instr
  | AStmt of 'mode stmt
  | ABlock of 'mode block
  | AFundec of 'mode fundec
  | AInit of 'mode init
  | AGlobal of 'mode global
  | AFile of 'mode file

type ground_file = ground file
type holed_file = holed file
type ground_ast = ground ast
type holed_ast = holed ast

let equal_list equal left right =
  List.length left = List.length right
  && List.for_all2 equal left right

let equal_option equal left right =
  match left, right with
  | None, None -> true
  | Some left, Some right -> equal left right
  | None, Some _ | Some _, None -> false

let rec equal_exp : type mode. mode exp -> mode exp -> bool =
 fun left right ->
  match left, right with
  | ExpHole left, ExpHole right -> Int.equal left right
  | Const left, Const right -> equal_constant left right
  | Lval left, Lval right -> equal_lval left right
  | UnOp (left_op, left_exp, left_typ),
    UnOp (right_op, right_exp, right_typ) ->
      equal_unop left_op right_op
      && equal_exp left_exp right_exp
      && Typ.equal left_typ right_typ
  | BinOp (left_op, left1, left2, left_typ),
    BinOp (right_op, right1, right2, right_typ) ->
      equal_binop left_op right_op
      && equal_exp left1 right1
      && equal_exp left2 right2
      && Typ.equal left_typ right_typ
  | AddrOf left, AddrOf right | StartOf left, StartOf right ->
      equal_lval left right
  | ExpHole _, _
  | Const _, _
  | Lval _, _
  | UnOp _, _
  | BinOp _, _
  | AddrOf _, _
  | StartOf _, _ ->
      false

and equal_lval : type mode. mode lval -> mode lval -> bool =
 fun (left_host, left_offset) (right_host, right_offset) ->
  equal_lhost left_host right_host
  && equal_offset left_offset right_offset

and equal_lhost : type mode. mode lhost -> mode lhost -> bool =
 fun left right ->
  match left, right with
  | Var left, Var right -> equal_varinfo left right
  | Mem left, Mem right -> equal_exp left right
  | Var _, _ | Mem _, _ -> false

and equal_offset : type mode. mode offset -> mode offset -> bool =
 fun left right ->
  match left, right with
  | NoOffset, NoOffset -> true
  | Field (left_field, left_offset), Field (right_field, right_offset) ->
      equal_fieldinfo left_field right_field
      && equal_offset left_offset right_offset
  | Index (left_exp, left_offset), Index (right_exp, right_offset) ->
      equal_exp left_exp right_exp
      && equal_offset left_offset right_offset
  | NoOffset, _ | Field _, _ | Index _, _ -> false

let equal_instr (type mode) (left : mode instr) (right : mode instr) =
  match left, right with
  | Set (left_lval, left_exp), Set (right_lval, right_exp) ->
      equal_lval left_lval right_lval
      && equal_exp left_exp right_exp
  | Call (left_return, left_callee, left_arguments),
    Call (right_return, right_callee, right_arguments) ->
      equal_option equal_lval left_return right_return
      && equal_exp left_callee right_callee
      && equal_list equal_exp left_arguments right_arguments
  | Set _, _ | Call _, _ -> false

let rec equal_block : type mode. mode block -> mode block -> bool =
 fun left right ->
  equal_list equal_stmt_seq_item left.bstmts right.bstmts

and equal_stmt_seq_item :
    type mode. mode stmt_seq_item -> mode stmt_seq_item -> bool =
 fun left right ->
  match left, right with
  | Stmt left, Stmt right -> equal_stmt left right
  | StmtSeqHole left, StmtSeqHole right -> Int.equal left right
  | Stmt _, _ | StmtSeqHole _, _ -> false

and equal_stmt : type mode. mode stmt -> mode stmt -> bool =
 fun left right ->
  equal_list equal_label left.labels right.labels
  && equal_stmtkind left.skind right.skind

and equal_stmtkind : type mode. mode stmtkind -> mode stmtkind -> bool =
 fun left right ->
  match left, right with
  | Instr left, Instr right -> equal_list equal_instr left right
  | Return left, Return right -> equal_option equal_exp left right
  | If (left_condition, left_then, left_else),
    If (right_condition, right_then, right_else) ->
      equal_exp left_condition right_condition
      && equal_block left_then right_then
      && equal_block left_else right_else
  | Loop left, Loop right | Block left, Block right ->
      equal_block left right
  | Break, Break | Continue, Continue -> true
  | Instr _, _
  | Return _, _
  | If _, _
  | Loop _, _
  | Break, _
  | Continue, _
  | Block _, _ ->
      false

let equal_fundec (type mode) (left : mode fundec)
    (right : mode fundec) =
  equal_varinfo left.svar right.svar
  && equal_list equal_varinfo left.sformals right.sformals
  && equal_list equal_varinfo left.slocals right.slocals
  && equal_block left.sbody right.sbody

let rec equal_init : type mode. mode init -> mode init -> bool =
 fun left right ->
  match left, right with
  | SingleInit left, SingleInit right -> equal_exp left right
  | CompoundInit (left_typ, left_fields),
    CompoundInit (right_typ, right_fields) ->
      Typ.equal left_typ right_typ
      && equal_list
           (fun (left_offset, left_init) (right_offset, right_init) ->
             equal_offset left_offset right_offset
             && equal_init left_init right_init)
           left_fields right_fields
  | SingleInit _, _ | CompoundInit _, _ -> false

let equal_initinfo (type mode) (left : mode initinfo)
    (right : mode initinfo) =
  equal_option equal_init left.init right.init

let equal_global (type mode) (left : mode global) (right : mode global) =
  match left, right with
  | GFun left, GFun right -> equal_fundec left right
  | GVarDecl left, GVarDecl right -> equal_varinfo left right
  | GVar (left_var, left_init), GVar (right_var, right_init) ->
      equal_varinfo left_var right_var
      && equal_initinfo left_init right_init
  | GFun _, _ | GVarDecl _, _ | GVar _, _ -> false

let equal_file (type mode) (left : mode file) (right : mode file) =
  String.equal left.fileName right.fileName
  && equal_list equal_global left.globals right.globals

let equal_ast (type mode) (left : mode ast) (right : mode ast) =
  match left, right with
  | AExp left, AExp right -> equal_exp left right
  | ALval left, ALval right -> equal_lval left right
  | AOffset left, AOffset right -> equal_offset left right
  | AInstr left, AInstr right -> equal_instr left right
  | AStmt left, AStmt right -> equal_stmt left right
  | ABlock left, ABlock right -> equal_block left right
  | AFundec left, AFundec right -> equal_fundec left right
  | AInit left, AInit right -> equal_init left right
  | AGlobal left, AGlobal right -> equal_global left right
  | AFile left, AFile right -> equal_file left right
  | AExp _, _
  | ALval _, _
  | AOffset _, _
  | AInstr _, _
  | AStmt _, _
  | ABlock _, _
  | AFundec _, _
  | AInit _, _
  | AGlobal _, _
  | AFile _, _ ->
      false

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

  type nonrec 'mode t = 'mode exp

  let equal_constant = equal_constant
  let equal_unop = equal_unop
  let equal_binop = equal_binop
  let equal_t = equal_exp

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

  let rec string_of_t : type mode. mode t -> string = function
    | ExpHole id -> Printf.sprintf "?H%d" id
    | Const constant -> string_of_constant constant
    | Lval lval -> string_of_lval lval
    | UnOp (op, exp, _) ->
        Printf.sprintf "(%s%s)" (string_of_unop op) (string_of_t exp)
    | BinOp (op, left, right, _) ->
        Printf.sprintf "(%s %s %s)" (string_of_t left)
          (string_of_binop op) (string_of_t right)
    | AddrOf lval -> "&" ^ string_of_lval lval
    | StartOf lval -> string_of_lval lval

  and string_of_lval : type mode. mode lval -> string =
   fun (host, offset) ->
    string_of_lhost host ^ string_of_offset offset

  and string_of_lhost : type mode. mode lhost -> string = function
    | Var var -> VarId.name var.vid
    | Mem exp -> "*" ^ string_of_t exp

  and string_of_offset : type mode. mode offset -> string = function
    | NoOffset -> ""
    | Field (field, offset) ->
        "." ^ field.fname ^ string_of_offset offset
    | Index (exp, offset) ->
        "[" ^ string_of_t exp ^ "]" ^ string_of_offset offset
end

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

let rec string_of_stmt : type mode. ?lvl:int -> mode stmt -> string =
 fun ?(lvl = 0) stmt ->
  let pad = indent lvl in
  let labels =
    List.map (fun label -> pad ^ string_of_label label) stmt.labels
  in
  let body = string_of_stmtkind ~lvl stmt.skind in
  let lines = if String.equal body "" then labels else labels @ [ body ] in
  String.concat "\n" lines

and string_of_stmtkind :
    type mode. ?lvl:int -> mode stmtkind -> string =
 fun ?(lvl = 0) -> function
  | Instr instrs ->
      instrs
      |> List.map (fun instr -> indent lvl ^ string_of_instr instr)
      |> String.concat "\n"
  | Return None -> indent lvl ^ "return;"
  | Return (Some e) -> indent lvl ^ "return " ^ Exp.string_of_t e ^ ";"
  | If (cond, tb, fb) ->
      Printf.sprintf "%sif (%s) %s else %s" (indent lvl)
        (Exp.string_of_t cond) (string_of_block ~lvl tb)
        (string_of_block ~lvl fb)
  | Loop body ->
      Printf.sprintf "%sloop %s" (indent lvl) (string_of_block ~lvl body)
  | Break -> indent lvl ^ "break;"
  | Continue -> indent lvl ^ "continue;"
  | Block block -> indent lvl ^ string_of_block ~lvl block

and string_of_stmt_seq_item :
    type mode. ?lvl:int -> mode stmt_seq_item -> string =
 fun ?(lvl = 0) -> function
  | Stmt stmt -> string_of_stmt ~lvl stmt
  | StmtSeqHole id -> Printf.sprintf "%s...?H%d" (indent lvl) id

and string_of_block : type mode. ?lvl:int -> mode block -> string =
 fun ?(lvl = 0) block ->
  let inner =
    List.map (string_of_stmt_seq_item ~lvl:(lvl + 1)) block.bstmts
  in
  match inner with
  | [] -> "{ }"
  | _ -> Printf.sprintf "{\n%s\n%s}" (String.concat "\n" inner) (indent lvl)

let string_of_fundec (type mode) (f : mode fundec) =
  let return_type =
    match f.svar.vtype with
    | Typ.TFun (return_type, _) -> return_type
    | _ -> invalid_arg "function svar must have a function type"
  in
  let params = String.concat ", " (List.map string_of_varinfo f.sformals) in
  Printf.sprintf "%s %s(%s) %s" (Typ.string_of_t return_type)
    (VarId.name f.svar.vid) params (string_of_block f.sbody)

let rec string_of_init : type mode. mode init -> string = function
  | SingleInit e -> Exp.string_of_t e
  | CompoundInit (_, fields) ->
      fields
      |> List.map (fun (_, init) -> string_of_init init)
      |> String.concat ", "
      |> Printf.sprintf "{ %s }"

let string_of_global (type mode) (global : mode global) =
  match global with
  | GFun f -> string_of_fundec f
  | GVarDecl v -> string_of_varinfo v ^ ";"
  | GVar (v, { init = None }) -> string_of_varinfo v ^ ";"
  | GVar (v, { init = Some init }) ->
      Printf.sprintf "%s = %s;" (string_of_varinfo v) (string_of_init init)

let string_of_file (type mode) (file : mode file) =
  file.globals |> List.map string_of_global |> String.concat "\n\n"
