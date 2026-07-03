open Syntax

let indent lvl = String.make (2 * lvl) ' '

let string_of_varinfo v =
  Printf.sprintf "%s %s" (Typ.string_of_t v.vtype) v.vname

module Exp = struct
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
    | Var v -> v.vname
    | Mem e -> "*" ^ string_of_t e

  and string_of_offset = function
    | NoOffset -> ""
    | Field (field, offset) -> "." ^ field.fname ^ string_of_offset offset
    | Index (e, offset) ->
        "[" ^ string_of_t e ^ "]" ^ string_of_offset offset
end

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
  let params = String.concat ", " (List.map string_of_varinfo f.sformals) in
  Printf.sprintf "%s %s(%s) %s" (Typ.string_of_t f.svar.vtype)
    f.svar.vname params (string_of_block f.sbody)

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
