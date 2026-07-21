open HoleSyntax

let var_name = SyntaxUtil.var_name
let string_of_var = SyntaxUtil.string_of_var

let name_of_global = function
  | GFun fundec -> var_name fundec.svar
  | GVarDecl var | GVar (var, _) -> var_name var

let function_return_type fundec =
  match fundec.svar.vtype with
  | Typ.TFun (return_type, _) -> return_type
  | _ -> invalid_arg "function svar must have a function type"

let is_void_type = SyntaxUtil.is_void_type

let main_functions file =
  List.filter_map
    (function
      | GFun fundec when String.equal (var_name fundec.svar) "main" ->
          Some fundec
      | _ -> None)
    file.globals
