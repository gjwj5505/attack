module S = Syntax

let indent lvl = String.make (2 * lvl) ' '

let string_of_varinfo v =
  Printf.sprintf "%s %s" (Typ.string_of_t v.S.vtype) v.S.vname

module Exp = struct
  let string_of_constant = function
    | S.Exp.CInt (n, Typ.IInt) -> Int64.to_string n
    | S.Exp.CInt (n, Typ.IUInt) -> Int64.to_string n ^ "U"

  let string_of_unop = function
    | S.Exp.Neg -> "-"
    | S.Exp.BNot -> "~"
    | S.Exp.LNot -> "!"

  let string_of_binop = function
    | S.Exp.PlusA -> "+"
    | S.Exp.PlusPI -> "+"
    | S.Exp.IndexPI -> "+"
    | S.Exp.MinusA -> "-"
    | S.Exp.MinusPI -> "-"
    | S.Exp.MinusPP -> "-"
    | S.Exp.Mult -> "*"
    | S.Exp.Div -> "/"
    | S.Exp.Mod -> "%"
    | S.Exp.Shiftlt -> "<<"
    | S.Exp.Shiftrt -> ">>"
    | S.Exp.Lt -> "<"
    | S.Exp.Gt -> ">"
    | S.Exp.Le -> "<="
    | S.Exp.Ge -> ">="
    | S.Exp.Eq -> "=="
    | S.Exp.Ne -> "!="
    | S.Exp.BAnd -> "&"
    | S.Exp.BXor -> "^"
    | S.Exp.BOr -> "|"
    | S.Exp.LAnd -> "&&"
    | S.Exp.LOr -> "||"

  let rec string_of_t = function
    | S.Exp.Const c -> string_of_constant c
    | S.Exp.Lval lv -> string_of_lval lv
    | S.Exp.UnOp (op, e, _) ->
        Printf.sprintf "(%s%s)" (string_of_unop op) (string_of_t e)
    | S.Exp.BinOp (op, e1, e2, _) ->
        Printf.sprintf "(%s %s %s)" (string_of_t e1) (string_of_binop op)
          (string_of_t e2)
    | S.Exp.AddrOf lv -> "&" ^ string_of_lval lv
    | S.Exp.StartOf lv -> string_of_lval lv

  and string_of_lval (host, offset) =
    string_of_lhost host ^ string_of_offset offset

  and string_of_lhost = function
    | S.Var v -> v.S.vname
    | S.Mem e -> "*" ^ string_of_t e

  and string_of_offset = function
    | S.NoOffset -> ""
    | S.Field (field, offset) -> "." ^ field.S.fname ^ string_of_offset offset
    | S.Index (e, offset) ->
        "[" ^ string_of_t e ^ "]" ^ string_of_offset offset
end

let string_of_lval = Exp.string_of_lval

let string_of_instr = function
  | S.Set (lv, e) ->
      Printf.sprintf "%s = %s;" (string_of_lval lv) (Exp.string_of_t e)
  | S.Call (ret, f, args) ->
      let ret =
        match ret with
        | None -> ""
        | Some lv -> string_of_lval lv ^ " = "
      in
      let args = args |> List.map Exp.string_of_t |> String.concat ", " in
      Printf.sprintf "%s%s(%s);" ret (Exp.string_of_t f) args

let string_of_label = function
  | S.Label name -> name ^ ":"

let rec string_of_stmt ?(lvl = 0) stmt =
  let pad = indent lvl in
  let labels =
    List.map (fun label -> pad ^ string_of_label label) stmt.S.labels
  in
  let body =
    match stmt.S.skind with
    | S.Instr instrs ->
        List.map (fun instr -> pad ^ string_of_instr instr) instrs
    | S.Return None -> [ pad ^ "return;" ]
    | S.Return (Some e) -> [ pad ^ "return " ^ Exp.string_of_t e ^ ";" ]
    | S.If (cond, tb, fb) ->
        [
          Printf.sprintf "%sif (%s) %s else %s" pad (Exp.string_of_t cond)
            (string_of_block ~lvl tb)
            (string_of_block ~lvl fb);
        ]
    | S.Loop body ->
        [ Printf.sprintf "%sloop %s" pad (string_of_block ~lvl body) ]
    | S.Break -> [ pad ^ "break;" ]
    | S.Continue -> [ pad ^ "continue;" ]
    | S.Block block -> [ pad ^ string_of_block ~lvl block ]
  in
  String.concat "\n" (labels @ body)

and string_of_block ?(lvl = 0) block =
  let inner = List.map (string_of_stmt ~lvl:(lvl + 1)) block.S.bstmts in
  match inner with
  | [] -> "{ }"
  | _ -> Printf.sprintf "{\n%s\n%s}" (String.concat "\n" inner) (indent lvl)

let string_of_fundec f =
  let params = String.concat ", " (List.map string_of_varinfo f.S.sformals) in
  Printf.sprintf "%s %s(%s) %s" (Typ.string_of_t f.S.svar.S.vtype)
    f.S.svar.S.vname params (string_of_block f.S.sbody)

let rec string_of_init = function
  | S.SingleInit e -> Exp.string_of_t e
  | S.CompoundInit (_, fields) ->
      fields
      |> List.map (fun (_, init) -> string_of_init init)
      |> String.concat ", "
      |> Printf.sprintf "{ %s }"

let string_of_global = function
  | S.GFun f -> string_of_fundec f
  | S.GVarDecl v -> string_of_varinfo v ^ ";"
  | S.GVar (v, { S.init = None }) -> string_of_varinfo v ^ ";"
  | S.GVar (v, { S.init = Some init }) ->
      Printf.sprintf "%s = %s;" (string_of_varinfo v) (string_of_init init)

let string_of_file file =
  file.S.globals |> List.map string_of_global |> String.concat "\n\n"
