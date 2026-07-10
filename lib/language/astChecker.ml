(* Structural checker for CIL-- abstract syntax. *)

module Cil = GoblintCil.Cil
module GoblintCheck = GoblintCil.Check

open Syntax
open SyntaxUtil

type error =
  | Bridge_error of CilBridge.error
  | Missing_main
  | Multiple_main
  | Invalid_main_type of Typ.t
  | Main_with_parameters
  | Invalid_function_type of varinfo
  | Function_formals_mismatch of {
      function_variable : varinfo;
      formals : varinfo list;
    }
  | Duplicate_global_name of string
  | Duplicate_function_local_name of {
      function_name : string;
      name : string;
    }
  | Global_local_name_collision of {
      function_name : string;
      name : string;
    }
  | Invalid_variable_scope of {
      variable : varinfo;
      expected : VarId.scope;
    }
  | Undeclared_variable of varinfo
  | Variable_declaration_mismatch of {
      occurrence : varinfo;
      declaration : varinfo;
    }
  | Break_outside_loop
  | Continue_outside_loop
  | Return_value_in_void_function
  | Return_without_value_in_nonvoid_function of Typ.t
  | Goblint_check_failed

let ( let* ) = Result.bind

let error x = Error x

let typ_equal = ( = )

module VarMap = Map.Make (VarId)

let rec check_list check = function
  | [] -> Ok ()
  | x :: xs ->
      let* () = check x in
      check_list check xs

let check_function_signatures file =
  let check_function fd =
    let actual_formals =
      List.map (fun formal -> (var_name formal, formal.vtype)) fd.sformals
    in
    match fd.svar.vtype with
    | Typ.TFun (_, Some declared_formals)
      when declared_formals = actual_formals ->
        Ok ()
    | Typ.TFun _ ->
        error
          (Function_formals_mismatch
             { function_variable = fd.svar; formals = fd.sformals })
    | _ -> error (Invalid_function_type fd.svar)
  in
  check_list
    (function
      | GFun fd -> check_function fd
      | GVarDecl _ | GVar _ -> Ok ())
    file.globals

let check_duplicate_global_names file =
  let seen = Hashtbl.create 16 in
  let rec loop = function
    | [] -> Ok ()
    | global :: globals ->
        let name = name_of_global global in
        if Hashtbl.mem seen name then error (Duplicate_global_name name)
        else (
          Hashtbl.add seen name ();
          loop globals )
  in
  loop file.globals

let check_duplicate_function_local_names file =
  let check_fundec fd =
    let seen = Hashtbl.create 16 in
    let check_var var =
      let name = var_name var in
      if Hashtbl.mem seen name then
        error
          (Duplicate_function_local_name
             { function_name = var_name fd.svar; name })
      else (
        Hashtbl.add seen name ();
        Ok () )
    in
    let rec loop = function
      | [] -> Ok ()
      | var :: vars ->
          let* () = check_var var in
          loop vars
    in
    let* () = loop fd.sformals in
    loop fd.slocals
  in
  let rec loop = function
    | [] -> Ok ()
    | GFun fd :: globals ->
        let* () = check_fundec fd in
        loop globals
    | (GVarDecl _ | GVar _) :: globals -> loop globals
  in
  loop file.globals

let check_global_local_name_collisions file =
  let global_names = Hashtbl.create 16 in
  List.iter
    (fun global -> Hashtbl.replace global_names (name_of_global global) ())
    file.globals;
  let check_function fd =
    let function_name = var_name fd.svar in
    check_list
      (fun variable ->
        let name = var_name variable in
        if Hashtbl.mem global_names name then
          error (Global_local_name_collision { function_name; name })
        else Ok ())
      (fd.sformals @ fd.slocals)
  in
  check_list
    (function
      | GFun fd -> check_function fd
      | GVarDecl _ | GVar _ -> Ok ())
    file.globals

let check_variable_scope expected variable =
  if VarId.scope variable.vid = expected then Ok ()
  else error (Invalid_variable_scope { variable; expected })

let check_variable_reference declarations occurrence =
  match VarMap.find_opt occurrence.vid declarations with
  | None -> error (Undeclared_variable occurrence)
  | Some declaration ->
      if SyntaxEqual.equal_varinfo occurrence declaration then Ok ()
      else
        error
          (Variable_declaration_mismatch { occurrence; declaration })

let rec check_exp_variables declarations = function
  | Exp.Const _ -> Ok ()
  | Exp.Lval lval -> check_lval_variables declarations lval
  | Exp.UnOp (_, exp, _) -> check_exp_variables declarations exp
  | Exp.BinOp (_, left, right, _) ->
      let* () = check_exp_variables declarations left in
      check_exp_variables declarations right
  | Exp.AddrOf lval | Exp.StartOf lval ->
      check_lval_variables declarations lval

and check_lval_variables declarations (host, offset) =
  let* () =
    match host with
    | Var variable -> check_variable_reference declarations variable
    | Mem exp -> check_exp_variables declarations exp
  in
  check_offset_variables declarations offset

and check_offset_variables declarations = function
  | NoOffset -> Ok ()
  | Field (_, offset) -> check_offset_variables declarations offset
  | Index (exp, offset) ->
      let* () = check_exp_variables declarations exp in
      check_offset_variables declarations offset

let check_instr_variables declarations = function
  | Set (lval, exp) ->
      let* () = check_lval_variables declarations lval in
      check_exp_variables declarations exp
  | Call (return_lval, callee, args) ->
      let* () =
        match return_lval with
        | None -> Ok ()
        | Some lval -> check_lval_variables declarations lval
      in
      let* () = check_exp_variables declarations callee in
      check_list (check_exp_variables declarations) args

let rec check_stmt_variables declarations stmt =
  match stmt.skind with
  | Instr instrs -> check_list (check_instr_variables declarations) instrs
  | Return None | Break | Continue -> Ok ()
  | Return (Some exp) -> check_exp_variables declarations exp
  | If (cond, then_block, else_block) ->
      let* () = check_exp_variables declarations cond in
      let* () = check_block_variables declarations then_block in
      check_block_variables declarations else_block
  | Loop body | Block body -> check_block_variables declarations body

and check_block_variables declarations block =
  check_list (check_stmt_variables declarations) block.bstmts

let rec check_init_variables declarations = function
  | SingleInit exp -> check_exp_variables declarations exp
  | CompoundInit (_, fields) ->
      check_list
        (fun (offset, init) ->
          let* () = check_offset_variables declarations offset in
          check_init_variables declarations init)
        fields

let check_variable_scopes file =
  let rec collect_globals declarations = function
    | [] -> Ok declarations
    | global :: globals ->
        let variable =
          match global with
          | GFun fd -> fd.svar
          | GVarDecl variable | GVar (variable, _) -> variable
        in
        let* () = check_variable_scope VarId.Global variable in
        collect_globals (VarMap.add variable.vid variable declarations) globals
  in
  let* globals = collect_globals VarMap.empty file.globals in
  let check_function fd =
    let function_name = var_name fd.svar in
    let expected_scope = VarId.Function function_name in
    let rec add_locals declarations = function
      | [] -> Ok declarations
      | variable :: variables ->
          let* () = check_variable_scope expected_scope variable in
          add_locals (VarMap.add variable.vid variable declarations) variables
    in
    let* declarations = add_locals globals fd.sformals in
    let* declarations = add_locals declarations fd.slocals in
    check_block_variables declarations fd.sbody
  in
  let check_global = function
    | GFun fd -> check_function fd
    | GVarDecl _ -> Ok ()
    | GVar (_, { init = None }) -> Ok ()
    | GVar (_, { init = Some init }) -> check_init_variables globals init
  in
  check_list check_global file.globals

let check_main file =
  match main_functions file with
  | [] -> error Missing_main
  | _ :: _ :: _ -> error Multiple_main
  | [ main ] ->
      let return_type = function_return_type main in
      if not (typ_equal return_type (Typ.TInt Typ.IInt)) then
        error (Invalid_main_type return_type)
      else if main.sformals <> [] then error Main_with_parameters
      else Ok ()

let rec check_block_control ~in_loop block =
  check_stmt_list_control ~in_loop block.bstmts

and check_stmt_list_control ~in_loop = function
  | [] -> Ok ()
  | stmt :: stmts ->
      let* () = check_stmt_control ~in_loop stmt in
      check_stmt_list_control ~in_loop stmts

and check_stmt_control ~in_loop stmt =
  match stmt.skind with
  | Break when not in_loop -> error Break_outside_loop
  | Continue when not in_loop -> error Continue_outside_loop
  | Break | Continue | Return _ | Instr _ -> Ok ()
  | If (_, then_block, else_block) ->
      let* () = check_block_control ~in_loop then_block in
      check_block_control ~in_loop else_block
  | Loop body -> check_block_control ~in_loop:true body
  | Block block -> check_block_control ~in_loop block

let check_control_flow file =
  let rec loop = function
    | [] -> Ok ()
    | GFun fd :: globals ->
        let* () = check_block_control ~in_loop:false fd.sbody in
        loop globals
    | (GVarDecl _ | GVar _) :: globals -> loop globals
  in
  loop file.globals

let rec check_block_returns ~return_type block =
  check_stmt_list_returns ~return_type block.bstmts

and check_stmt_list_returns ~return_type = function
  | [] -> Ok ()
  | stmt :: stmts ->
      let* () = check_stmt_returns ~return_type stmt in
      check_stmt_list_returns ~return_type stmts

and check_stmt_returns ~return_type stmt =
  match stmt.skind with
  | Return None when not (is_void_type return_type) ->
      error (Return_without_value_in_nonvoid_function return_type)
  | Return (Some _) when is_void_type return_type ->
      error Return_value_in_void_function
  | Return _ | Break | Continue | Instr _ -> Ok ()
  | If (_, then_block, else_block) ->
      let* () = check_block_returns ~return_type then_block in
      check_block_returns ~return_type else_block
  | Loop body -> check_block_returns ~return_type body
  | Block block -> check_block_returns ~return_type block

let check_returns file =
  let rec loop = function
    | [] -> Ok ()
    | GFun fd :: globals ->
        let* () =
          check_block_returns ~return_type:(function_return_type fd) fd.sbody
        in
        loop globals
    | (GVarDecl _ | GVar _) :: globals -> loop globals
  in
  loop file.globals

let check_roundtrip file =
  match CilBridge.check_roundtrip_file file with
  | Ok () -> Ok ()
  | Error err -> error (Bridge_error err)

let check_goblint file =
  let* cil_file =
    match CilBridge.file_to_cil file with
    | Ok cil_file -> Ok cil_file
    | Error err -> error (Bridge_error err)
  in
  Cil.insertImplicitCasts := true;
  if GoblintCheck.checkFile [] cil_file then Ok ()
  else error Goblint_check_failed

let check_file file =
  let* () = check_function_signatures file in
  let* () = check_main file in
  let* () = check_duplicate_global_names file in
  let* () = check_duplicate_function_local_names file in
  let* () = check_global_local_name_collisions file in
  let* () = check_variable_scopes file in
  let* () = check_control_flow file in
  let* () = check_returns file in
  let* () = check_roundtrip file in
  check_goblint file
  (* Expected GoblintCil.Check coverage:
   - expression and assignment type errors
   - invalid implicit conversions
   - invalid function call arity or argument types
   - undeclared identifiers
   - calls without a valid prior declaration under the C front-end rules
   - invalid return types beyond the CIL-- return-shape check above
   - other C-level constraints that require GoblintCil's typing environment

   Directly synthesized CIL-- can bypass parser/front-end assumptions. Add
   explicit CIL-- checks above when a property is required by our semantics rather
   than merely by source-C compatibility. *)

let string_of_error = function
  | Bridge_error err -> CilBridge.string_of_error err
  | Missing_main -> "missing main function"
  | Multiple_main -> "multiple main functions"
  | Invalid_main_type typ ->
      "invalid main return type: " ^ Typ.string_of_t typ
  | Main_with_parameters -> "main must have no parameters"
  | Invalid_function_type function_variable ->
      Printf.sprintf "function variable %s has non-function type: %s"
        (string_of_var function_variable)
        (Typ.string_of_t function_variable.vtype)
  | Function_formals_mismatch { function_variable; formals } ->
      let formals =
        formals
        |> List.map (fun formal ->
               Typ.string_of_t formal.vtype ^ " " ^ var_name formal)
        |> String.concat ", "
      in
      Printf.sprintf
        "function formals mismatch for %s: declared type %s, formals (%s)"
        (string_of_var function_variable)
        (Typ.string_of_t function_variable.vtype)
        formals
  | Duplicate_global_name name -> "duplicate global name: " ^ name
  | Duplicate_function_local_name { function_name; name } ->
      Printf.sprintf "duplicate local name in %s: %s" function_name name
  | Global_local_name_collision { function_name; name } ->
      Printf.sprintf "global/local name collision in %s: %s" function_name name
  | Invalid_variable_scope { variable; expected } ->
      let expected =
        match expected with
        | VarId.Global -> "global"
        | VarId.Function function_name -> "function " ^ function_name
      in
      Printf.sprintf "invalid scope for %s: expected %s" (string_of_var variable)
        expected
  | Undeclared_variable variable ->
      "undeclared variable: " ^ string_of_var variable
  | Variable_declaration_mismatch { occurrence; declaration } ->
      Printf.sprintf "variable declaration mismatch: %s does not match %s"
        (string_of_var occurrence) (string_of_var declaration)
  | Break_outside_loop -> "break outside loop"
  | Continue_outside_loop -> "continue outside loop"
  | Return_value_in_void_function -> "return value in void function"
  | Return_without_value_in_nonvoid_function typ ->
      "return without value in non-void function: " ^ Typ.string_of_t typ
  | Goblint_check_failed -> "GoblintCil.Check.checkFile failed"
