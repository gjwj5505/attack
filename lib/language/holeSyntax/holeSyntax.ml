(* CIL-- syntax that may contain expression and statement-sequence holes. *)

type hole_id = int

type id = Syntax.id

module VarId = Syntax.VarId

type varinfo = Syntax.varinfo
type fieldinfo = Syntax.fieldinfo
type constant = Syntax.constant
type unop = Syntax.unop
type binop = Syntax.binop

type exp =
  | ExpHole of hole_id
  | Const of constant
  | Lval of lval
  | UnOp of unop * exp * Typ.t
  | BinOp of binop * exp * exp * Typ.t
  | AddrOf of lval
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
  type nonrec constant = constant
  type nonrec unop = unop
  type nonrec binop = binop

  type nonrec t = exp =
    | ExpHole of hole_id
    | Const of constant
    | Lval of lval
    | UnOp of unop * exp * Typ.t
    | BinOp of binop * exp * exp * Typ.t
    | AddrOf of lval
    | StartOf of lval

  let string_of_constant = Syntax.Exp.string_of_constant
  let string_of_unop = Syntax.Exp.string_of_unop
  let string_of_binop = Syntax.Exp.string_of_binop

  let string_of_hole id = Printf.sprintf "?H%d" id

  let rec string_of_t = function
    | ExpHole id -> string_of_hole id
    | Const constant -> string_of_constant constant
    | Lval lval -> string_of_lval lval
    | UnOp (op, exp, _) ->
        Printf.sprintf "(%s%s)" (string_of_unop op) (string_of_t exp)
    | BinOp (op, left, right, _) ->
        Printf.sprintf "(%s %s %s)" (string_of_t left) (string_of_binop op)
          (string_of_t right)
    | AddrOf lval -> "&" ^ string_of_lval lval
    | StartOf lval -> string_of_lval lval

  and string_of_lval (host, offset) =
    string_of_lhost host ^ string_of_offset offset

  and string_of_lhost = function
    | Var var -> VarId.name var.vid
    | Mem exp -> "*" ^ string_of_t exp

  and string_of_offset = function
    | NoOffset -> ""
    | Field (field, offset) -> "." ^ field.fname ^ string_of_offset offset
    | Index (exp, offset) ->
        "[" ^ string_of_t exp ^ "]" ^ string_of_offset offset
end

type instr =
  | Set of lval * Exp.t
  | Call of lval option * Exp.t * Exp.t list

type label = Syntax.label

(** The outer [bstmts] list of each block contains at most one direct
    [StmtSeqHole], and it must be the final item. Nested blocks and other proof
    conclusions may contain their own holes. *)
type block = {
  bstmts : stmt_seq_item list;
}

and stmt_seq_item =
  | Stmt of stmt
  | StmtSeqHole of hole_id

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

type init =
  | SingleInit of Exp.t
  | CompoundInit of Typ.t * (offset * init) list

type initinfo = {
  init : init option;
}

type global =
  | GFun of fundec
  | GVarDecl of varinfo
  | GVar of varinfo * initinfo

type file = {
  fileName : string;
  globals : global list;
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

let indent = Syntax.indent
let string_of_varinfo = Syntax.string_of_varinfo
let string_of_lval = Exp.string_of_lval

let string_of_instr = function
  | Set (lval, exp) ->
      Printf.sprintf "%s = %s;" (string_of_lval lval) (Exp.string_of_t exp)
  | Call (ret, callee, args) ->
      let ret =
        match ret with
        | None -> ""
        | Some lval -> string_of_lval lval ^ " = "
      in
      let args = args |> List.map Exp.string_of_t |> String.concat ", " in
      Printf.sprintf "%s%s(%s);" ret (Exp.string_of_t callee) args

let string_of_label = Syntax.string_of_label

let rec string_of_stmt ?(lvl = 0) stmt =
  let pad = indent lvl in
  let labels =
    List.map (fun label -> pad ^ string_of_label label) stmt.labels
  in
  let body = string_of_stmtkind ~lvl stmt.skind in
  let lines = if String.equal body "" then labels else labels @ [ body ] in
  String.concat "\n" lines

and string_of_stmtkind ?(lvl = 0) = function
  | Instr instrs ->
      instrs
      |> List.map (fun instr -> indent lvl ^ string_of_instr instr)
      |> String.concat "\n"
  | Return None -> indent lvl ^ "return;"
  | Return (Some exp) ->
      indent lvl ^ "return " ^ Exp.string_of_t exp ^ ";"
  | If (condition, then_block, else_block) ->
      Printf.sprintf "%sif (%s) %s else %s" (indent lvl)
        (Exp.string_of_t condition)
        (string_of_block ~lvl then_block)
        (string_of_block ~lvl else_block)
  | Loop body ->
      Printf.sprintf "%sloop %s" (indent lvl) (string_of_block ~lvl body)
  | Break -> indent lvl ^ "break;"
  | Continue -> indent lvl ^ "continue;"
  | Block block -> indent lvl ^ string_of_block ~lvl block

and string_of_stmt_seq_item ?(lvl = 0) = function
  | Stmt stmt -> string_of_stmt ~lvl stmt
  | StmtSeqHole id -> Printf.sprintf "%s...?H%d" (indent lvl) id

and string_of_block ?(lvl = 0) block =
  let inner =
    List.map (string_of_stmt_seq_item ~lvl:(lvl + 1)) block.bstmts
  in
  match inner with
  | [] -> "{ }"
  | _ -> Printf.sprintf "{\n%s\n%s}" (String.concat "\n" inner) (indent lvl)

let string_of_fundec fundec =
  let return_type =
    match fundec.svar.vtype with
    | Typ.TFun (return_type, _) -> return_type
    | _ -> invalid_arg "function svar must have a function type"
  in
  let params =
    String.concat ", " (List.map string_of_varinfo fundec.sformals)
  in
  Printf.sprintf "%s %s(%s) %s" (Typ.string_of_t return_type)
    (VarId.name fundec.svar.vid) params (string_of_block fundec.sbody)

let rec string_of_init = function
  | SingleInit exp -> Exp.string_of_t exp
  | CompoundInit (_, fields) ->
      fields
      |> List.map (fun (_, init) -> string_of_init init)
      |> String.concat ", "
      |> Printf.sprintf "{ %s }"

let string_of_global = function
  | GFun fundec -> string_of_fundec fundec
  | GVarDecl var -> string_of_varinfo var ^ ";"
  | GVar (var, { init = None }) -> string_of_varinfo var ^ ";"
  | GVar (var, { init = Some init }) ->
      Printf.sprintf "%s = %s;" (string_of_varinfo var) (string_of_init init)

let string_of_file file =
  file.globals |> List.map string_of_global |> String.concat "\n\n"
