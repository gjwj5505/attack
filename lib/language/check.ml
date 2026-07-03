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
  | Duplicate_global_name of string
  | Break_outside_loop
  | Continue_outside_loop
  | Return_value_in_void_function
  | Return_without_value_in_nonvoid_function of Typ.t
  | Goblint_check_failed

let ( let* ) = Result.bind

let error x = Error x

let typ_equal = ( = )

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

let check_main file =
  match main_functions file with
  | [] -> error Missing_main
  | _ :: _ :: _ -> error Multiple_main
  | [ main ] ->
      if not (typ_equal main.svar.vtype (Typ.TInt Typ.IInt)) then
        error (Invalid_main_type main.svar.vtype)
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
  let* () = check_main file in
  let* () = check_duplicate_global_names file in
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
   - invalid return types beyond the CIL' return-shape check above
   - other C-level constraints that require GoblintCil's typing environment

   Directly synthesized CIL' can bypass parser/front-end assumptions. Add
   explicit CIL' checks above when a property is required by our semantics rather
   than merely by source-C compatibility. *)

let string_of_error = function
  | Bridge_error err -> CilBridge.string_of_error err
  | Missing_main -> "missing main function"
  | Multiple_main -> "multiple main functions"
  | Invalid_main_type typ ->
      "invalid main return type: " ^ Typ.string_of_t typ
  | Main_with_parameters -> "main must have no parameters"
  | Duplicate_global_name name -> "duplicate global name: " ^ name
  | Break_outside_loop -> "break outside loop"
  | Continue_outside_loop -> "continue outside loop"
  | Return_value_in_void_function -> "return value in void function"
  | Return_without_value_in_nonvoid_function typ ->
      "return without value in non-void function: " ^ Typ.string_of_t typ
  | Goblint_check_failed -> "GoblintCil.Check.checkFile failed"
