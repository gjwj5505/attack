open Syntax

let string_of_var var = Printf.sprintf "%s#%d" var.vname var.vid

let name_of_global = function
  | GFun fd -> fd.svar.vname
  | GVarDecl var -> var.vname
  | GVar (var, _) -> var.vname

let function_return_type fd = fd.svar.vtype

let is_void_type = function
  | Typ.TVoid -> true
  | _ -> false

let main_functions file =
  List.filter_map
    (function
      | GFun fd when String.equal fd.svar.vname "main" -> Some fd
      | _ -> None)
    file.globals
