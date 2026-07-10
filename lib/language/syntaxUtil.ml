open Syntax

let var_name var = VarId.name var.vid

let string_of_var var =
  match VarId.scope var.vid with
  | VarId.Global -> var_name var
  | VarId.Function function_name -> function_name ^ "::" ^ var_name var

let name_of_global = function
  | GFun fd -> var_name fd.svar
  | GVarDecl var | GVar (var, _) -> var_name var

let function_return_type fd =
  match fd.svar.vtype with
  | Typ.TFun (return_type, _) -> return_type
  | _ -> invalid_arg "function svar must have a function type"

let is_void_type = function
  | Typ.TVoid -> true
  | _ -> false

let main_functions file =
  List.filter_map
    (function
      | GFun fd when String.equal (var_name fd.svar) "main" -> Some fd
      | _ -> None)
    file.globals
