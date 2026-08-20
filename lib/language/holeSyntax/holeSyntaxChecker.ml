(* Structural checker for CIL-- syntax that may still contain holes. *)

open Syntax
open SyntaxUtil

type hole_sort =
  | Expression
  | Statement_sequence

type error =
  | Syntax_error of SyntaxChecker.error
  | Invalid_hole_id of hole_id
  | Duplicate_hole_id of hole_id
  | Hole_sort_mismatch of {
      id : hole_id;
      expected : hole_sort;
      actual : hole_sort;
    }
  | Multiple_direct_stmt_seq_holes of hole_id list
  | Nonfinal_stmt_seq_hole of hole_id

let string_of_hole_sort = function
  | Expression -> "expression"
  | Statement_sequence -> "statement sequence"

let string_of_error = function
  | Syntax_error error -> SyntaxChecker.string_of_error error
  | Invalid_hole_id id ->
      Printf.sprintf "invalid hole ID H%d: expected a positive integer" id
  | Duplicate_hole_id id ->
      Printf.sprintf "hole H%d occurs more than once in one AST" id
  | Hole_sort_mismatch { id; expected; actual } ->
      Printf.sprintf "hole H%d has sort %s, but also occurs with sort %s" id
        (string_of_hole_sort expected)
        (string_of_hole_sort actual)
  | Multiple_direct_stmt_seq_holes ids ->
      Printf.sprintf "one block contains multiple direct statement-sequence holes: %s"
        (ids
        |> List.map (Printf.sprintf "H%d")
        |> String.concat ", ")
  | Nonfinal_stmt_seq_hole id ->
      Printf.sprintf "direct statement-sequence hole H%d is not final in its block"
        id

let ( let* ) = Result.bind
let error error = Error error
let syntax_error error = Error (Syntax_error error)
let lift_syntax_error result =
  Result.map_error (fun error -> Syntax_error error) result

let rec check_list check = function
  | [] -> Ok ()
  | item :: rest ->
      let* () = check item in
      check_list check rest

module HoleMap = Map.Make (Int)
module VarMap = SyntaxChecker.VarMap

let register_hole sort id holes =
  if id <= 0 then error (Invalid_hole_id id)
  else
    match HoleMap.find_opt id holes with
    | None -> Ok (HoleMap.add id sort holes)
    | Some expected when expected = sort -> error (Duplicate_hole_id id)
    | Some expected -> error (Hole_sort_mismatch { id; expected; actual = sort })

let rec check_state_list check holes = function
  | [] -> Ok holes
  | item :: rest ->
      let* holes = check holes item in
      check_state_list check holes rest

let check_state_option check holes = function
  | None -> Ok holes
  | Some item -> check holes item

let rec check_exp_holes holes = function
  | ExpHole id -> register_hole Expression id holes
  | Const _ -> Ok holes
  | Lval lval | AddrOf lval | StartOf lval -> check_lval_holes holes lval
  | UnOp (_, exp, _) -> check_exp_holes holes exp
  | BinOp (_, left, right, _) ->
      let* holes = check_exp_holes holes left in
      check_exp_holes holes right

and check_lval_holes holes (host, offset) =
  let* holes = check_lhost_holes holes host in
  check_offset_holes holes offset

and check_lhost_holes holes = function
  | Var _ -> Ok holes
  | Mem exp -> check_exp_holes holes exp

and check_offset_holes holes = function
  | NoOffset -> Ok holes
  | Field (_, offset) -> check_offset_holes holes offset
  | Index (exp, offset) ->
      let* holes = check_exp_holes holes exp in
      check_offset_holes holes offset

let check_instr_holes holes = function
  | Set (lval, exp) ->
      let* holes = check_lval_holes holes lval in
      check_exp_holes holes exp
  | Call (ret, callee, args) ->
      let* holes = check_state_option check_lval_holes holes ret in
      let* holes = check_exp_holes holes callee in
      check_state_list check_exp_holes holes args

let direct_stmt_seq_hole_ids block =
  List.filter_map
    (function
      | Stmt _ -> None
      | StmtSeqHole id -> Some id)
    block.bstmts

let rec find_nonfinal_stmt_seq_hole = function
  | [] | [ _ ] -> None
  | StmtSeqHole id :: _ -> Some id
  | Stmt _ :: rest -> find_nonfinal_stmt_seq_hole rest

let check_block_shape block =
  let ids = direct_stmt_seq_hole_ids block in
  match ids with
  | _ :: _ :: _ -> error (Multiple_direct_stmt_seq_holes ids)
  | _ -> (
      match find_nonfinal_stmt_seq_hole block.bstmts with
      | Some id -> error (Nonfinal_stmt_seq_hole id)
      | None -> Ok ())

let rec check_stmt_holes holes stmt = check_stmtkind_holes holes stmt.skind

and check_stmt_seq_item_holes holes = function
  | Stmt stmt -> check_stmt_holes holes stmt
  | StmtSeqHole id -> register_hole Statement_sequence id holes

and check_stmtkind_holes holes = function
  | Instr instrs -> check_state_list check_instr_holes holes instrs
  | Return exp -> check_state_option check_exp_holes holes exp
  | If (condition, then_block, else_block) ->
      let* holes = check_exp_holes holes condition in
      let* holes = check_block_holes holes then_block in
      check_block_holes holes else_block
  | Loop body | Block body -> check_block_holes holes body
  | Break | Continue -> Ok holes

and check_block_holes holes block =
  let* () = check_block_shape block in
  check_state_list check_stmt_seq_item_holes holes block.bstmts

let check_fundec_holes holes fundec = check_block_holes holes fundec.sbody

let rec check_init_holes holes = function
  | SingleInit exp -> check_exp_holes holes exp
  | CompoundInit (_, fields) ->
      check_state_list
        (fun holes (offset, init) ->
          let* holes = check_offset_holes holes offset in
          check_init_holes holes init)
        holes fields

let check_initinfo_holes holes initinfo =
  check_state_option check_init_holes holes initinfo.init

let check_global_holes holes = function
  | GFun fundec -> check_fundec_holes holes fundec
  | GVarDecl _ -> Ok holes
  | GVar (_, initinfo) -> check_initinfo_holes holes initinfo

let check_file_holes holes file =
  check_state_list check_global_holes holes file.globals

let check_ast_holes holes = function
  | AExp exp -> check_exp_holes holes exp
  | ALval lval -> check_lval_holes holes lval
  | AOffset offset -> check_offset_holes holes offset
  | AInstr instr -> check_instr_holes holes instr
  | AStmt stmt -> check_stmt_holes holes stmt
  | ABlock block -> check_block_holes holes block
  | AFundec fundec -> check_fundec_holes holes fundec
  | AInit init -> check_init_holes holes init
  | AGlobal global -> check_global_holes holes global
  | AFile file -> check_file_holes holes file

let run_hole_check check value =
  Result.map (fun _ -> ()) (check HoleMap.empty value)

let check_exp = run_hole_check check_exp_holes
let check_lval = run_hole_check check_lval_holes
let check_offset = run_hole_check check_offset_holes
let check_instr = run_hole_check check_instr_holes
let check_stmt = run_hole_check check_stmt_holes
let check_block = run_hole_check check_block_holes
let check_fundec = run_hole_check check_fundec_holes
let check_init = run_hole_check check_init_holes
let check_global = run_hole_check check_global_holes
let check_ast = run_hole_check check_ast_holes

let check_function_signatures file =
  let check_function fundec =
    let actual_formals =
      List.map
        (fun formal -> (var_name formal, formal.vtype))
        fundec.sformals
    in
    match fundec.svar.vtype with
    | Typ.TFun (_, Some declared_formals)
      when declared_formals = actual_formals ->
        Ok ()
    | Typ.TFun _ ->
        syntax_error
          (SyntaxChecker.Function_formals_mismatch
             { function_variable = fundec.svar; formals = fundec.sformals })
    | _ -> syntax_error (SyntaxChecker.Invalid_function_type fundec.svar)
  in
  check_list
    (function
      | GFun fundec -> check_function fundec
      | GVarDecl _ | GVar _ -> Ok ())
    file.globals

let check_duplicate_global_names file =
  let seen = Hashtbl.create 16 in
  let rec loop = function
    | [] -> Ok ()
    | global :: globals ->
        let name = name_of_global global in
        if Hashtbl.mem seen name then
          syntax_error (SyntaxChecker.Duplicate_global_name name)
        else (
          Hashtbl.add seen name ();
          loop globals )
  in
  loop file.globals

let check_duplicate_function_local_names file =
  let check_fundec fundec =
    let seen = Hashtbl.create 16 in
    let check_var var =
      let name = var_name var in
      if Hashtbl.mem seen name then
        syntax_error
          (SyntaxChecker.Duplicate_function_local_name
             { function_name = var_name fundec.svar; name })
      else (
        Hashtbl.add seen name ();
        Ok () )
    in
    let* () = check_list check_var fundec.sformals in
    check_list check_var fundec.slocals
  in
  check_list
    (function
      | GFun fundec -> check_fundec fundec
      | GVarDecl _ | GVar _ -> Ok ())
    file.globals

let check_global_local_name_collisions file =
  let global_names = Hashtbl.create 16 in
  List.iter
    (fun global -> Hashtbl.replace global_names (name_of_global global) ())
    file.globals;
  let check_function fundec =
    let function_name = var_name fundec.svar in
    check_list
      (fun variable ->
        let name = var_name variable in
        if Hashtbl.mem global_names name then
          syntax_error
            (SyntaxChecker.Global_local_name_collision { function_name; name })
        else Ok ())
      (fundec.sformals @ fundec.slocals)
  in
  check_list
    (function
      | GFun fundec -> check_function fundec
      | GVarDecl _ | GVar _ -> Ok ())
    file.globals

let check_variable_scope expected variable =
  lift_syntax_error (SyntaxChecker.check_variable_scope expected variable)

let check_variable_reference declarations occurrence =
  lift_syntax_error
    (SyntaxChecker.check_variable_reference declarations occurrence)

let rec check_exp_variables declarations = function
  | ExpHole _ | Const _ -> Ok ()
  | Lval lval | AddrOf lval | StartOf lval ->
      check_lval_variables declarations lval
  | UnOp (_, exp, _) -> check_exp_variables declarations exp
  | BinOp (_, left, right, _) ->
      let* () = check_exp_variables declarations left in
      check_exp_variables declarations right

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
  | Call (ret, callee, args) ->
      let* () =
        match ret with
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
  | If (condition, then_block, else_block) ->
      let* () = check_exp_variables declarations condition in
      let* () = check_block_variables declarations then_block in
      check_block_variables declarations else_block
  | Loop body | Block body -> check_block_variables declarations body

and check_stmt_seq_item_variables declarations = function
  | Stmt stmt -> check_stmt_variables declarations stmt
  | StmtSeqHole _ -> Ok ()

and check_block_variables declarations block =
  check_list (check_stmt_seq_item_variables declarations) block.bstmts

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
          | GFun fundec -> fundec.svar
          | GVarDecl variable | GVar (variable, _) -> variable
        in
        let* () = check_variable_scope VarId.Global variable in
        collect_globals (VarMap.add variable.vid variable declarations) globals
  in
  let* globals = collect_globals VarMap.empty file.globals in
  let check_function fundec =
    let function_name = var_name fundec.svar in
    let expected_scope = VarId.Function function_name in
    let rec add_locals declarations = function
      | [] -> Ok declarations
      | variable :: variables ->
          let* () = check_variable_scope expected_scope variable in
          add_locals (VarMap.add variable.vid variable declarations) variables
    in
    let* declarations = add_locals globals fundec.sformals in
    let* declarations = add_locals declarations fundec.slocals in
    check_block_variables declarations fundec.sbody
  in
  let check_global = function
    | GFun fundec -> check_function fundec
    | GVarDecl _ -> Ok ()
    | GVar (_, { init = None }) -> Ok ()
    | GVar (_, { init = Some init }) -> check_init_variables globals init
  in
  check_list check_global file.globals

let check_main file =
  match main_functions file with
  | [] -> syntax_error SyntaxChecker.Missing_main
  | _ :: _ :: _ -> syntax_error SyntaxChecker.Multiple_main
  | [ main ] ->
      let return_type = function_return_type main in
      if return_type <> Typ.TInt Typ.IInt then
        syntax_error (SyntaxChecker.Invalid_main_type return_type)
      else if main.sformals <> [] then
        syntax_error SyntaxChecker.Main_with_parameters
      else Ok ()

let rec check_block_control ~in_loop block =
  check_list (check_stmt_seq_item_control ~in_loop) block.bstmts

and check_stmt_seq_item_control ~in_loop = function
  | Stmt stmt -> check_stmt_control ~in_loop stmt
  | StmtSeqHole _ -> Ok ()

and check_stmt_control ~in_loop stmt =
  match stmt.skind with
  | Break when not in_loop -> syntax_error SyntaxChecker.Break_outside_loop
  | Continue when not in_loop ->
      syntax_error SyntaxChecker.Continue_outside_loop
  | Break | Continue | Return _ | Instr _ -> Ok ()
  | If (_, then_block, else_block) ->
      let* () = check_block_control ~in_loop then_block in
      check_block_control ~in_loop else_block
  | Loop body -> check_block_control ~in_loop:true body
  | Block block -> check_block_control ~in_loop block

let check_control_flow file =
  check_list
    (function
      | GFun fundec -> check_block_control ~in_loop:false fundec.sbody
      | GVarDecl _ | GVar _ -> Ok ())
    file.globals

let rec check_block_returns ~return_type block =
  check_list (check_stmt_seq_item_returns ~return_type) block.bstmts

and check_stmt_seq_item_returns ~return_type = function
  | Stmt stmt -> check_stmt_returns ~return_type stmt
  | StmtSeqHole _ -> Ok ()

and check_stmt_returns ~return_type stmt =
  match stmt.skind with
  | Return None when not (is_void_type return_type) ->
      syntax_error
        (SyntaxChecker.Return_without_value_in_nonvoid_function return_type)
  | Return (Some _) when is_void_type return_type ->
      syntax_error SyntaxChecker.Return_value_in_void_function
  | Return _ | Break | Continue | Instr _ -> Ok ()
  | If (_, then_block, else_block) ->
      let* () = check_block_returns ~return_type then_block in
      check_block_returns ~return_type else_block
  | Loop body -> check_block_returns ~return_type body
  | Block block -> check_block_returns ~return_type block

let check_returns file =
  check_list
    (function
      | GFun fundec ->
          check_block_returns ~return_type:(function_return_type fundec)
            fundec.sbody
      | GVarDecl _ | GVar _ -> Ok ())
    file.globals

let check_file file =
  let* () = run_hole_check check_file_holes file in
  let* () = check_function_signatures file in
  let* () = check_main file in
  let* () = check_duplicate_global_names file in
  let* () = check_duplicate_function_local_names file in
  let* () = check_global_local_name_collisions file in
  let* () = check_variable_scopes file in
  let* () = check_control_flow file in
  check_returns file

(* CIL roundtrip and GoblintCil.Check require a complete concrete Syntax.file.
   Final materialization validates those properties with SyntaxChecker. *)
