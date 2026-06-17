(*
 * Syntax for the Sparrow-facing C subset.
 *)

type id = string

type binding = {
  typ : Typ.t;
  name : id;
}

type lval =
  | LVar of id

module Exp = struct
  type uop = Uminus

  type bop =
    | Eq
    | Ne
    | Lt
    | Le
    | Gt
    | Ge
    | Plus
    | Minus
    | Times
    | Div
    | Mod

  type t =
    | Int of Int64.t
    | Lval of lval
    | Uop of uop * t
    | Bop of bop * t * t

  let string_of_uop = function
    | Uminus -> "-"

  let string_of_bop = function
    | Eq -> "=="
    | Ne -> "!="
    | Lt -> "<"
    | Le -> "<="
    | Gt -> ">"
    | Ge -> ">="
    | Plus -> "+"
    | Minus -> "-"
    | Times -> "*"
    | Div -> "/"
    | Mod -> "%"

  let rec string_of_t = function
    | Int n -> Int64.to_string n
    | Lval lv -> string_of_lval lv
    | Uop (op, e) -> Printf.sprintf "(%s%s)" (string_of_uop op) (string_of_t e)
    | Bop (op, e1, e2) ->
        Printf.sprintf "(%s %s %s)" (string_of_t e1) (string_of_bop op)
          (string_of_t e2)

  and string_of_lval = function
    | LVar id -> id
end

let string_of_lval = Exp.string_of_lval

let string_of_binding { typ; name } =
  Printf.sprintf "%s %s" (Typ.string_of_t typ) name

module Stmt = struct
  type t =
    | Decl of binding * Exp.t
    | Assign of lval * Exp.t
    | If of Exp.t * codeblock * codeblock
    | While of Exp.t * codeblock
    | Return of Exp.t

  and codeblock = t list

  let indent lvl = String.make (2 * lvl) ' '

  let rec string_of_t ?(lvl = 0) stmt =
    let pad = indent lvl in
    match stmt with
    | Decl (binding, e) ->
        Printf.sprintf "%s%s = %s;" pad (string_of_binding binding)
          (Exp.string_of_t e)
    | Assign (lv, e) ->
        Printf.sprintf "%s%s = %s;" pad (string_of_lval lv) (Exp.string_of_t e)
    | If (cond, tb, fb) ->
        Printf.sprintf "%sif (%s) %s else %s" pad (Exp.string_of_t cond)
          (string_of_codeblock ~lvl tb)
          (string_of_codeblock ~lvl fb)
    | While (cond, body) ->
        Printf.sprintf "%swhile (%s) %s" pad (Exp.string_of_t cond)
          (string_of_codeblock ~lvl body)
    | Return e -> Printf.sprintf "%sreturn %s;" pad (Exp.string_of_t e)

  and string_of_codeblock ?(lvl = 0) stmts =
    let inner = List.map (string_of_t ~lvl:(lvl + 1)) stmts in
    match inner with
    | [] -> "{ }"
    | _ ->
        Printf.sprintf "{\n%s\n%s}" (String.concat "\n" inner) (indent lvl)
end

type func = {
  ret_type : Typ.t;
  name : id;
  params : binding list;
  body : Stmt.codeblock;
}

type program = {
  main : func;
}

let string_of_param = string_of_binding

let string_of_func f =
  let params = String.concat ", " (List.map string_of_param f.params) in
  Printf.sprintf "%s %s(%s) %s" (Typ.string_of_t f.ret_type) f.name params
    (Stmt.string_of_codeblock f.body)

let string_of_program { main } = string_of_func main
