open Syntax

module Substitution = HoleSubstitution

type error =
  | Substitution_error of Substitution.error
  | Expression_mismatch of holed exp * holed exp
  | Lhost_mismatch of holed lhost * holed lhost
  | Offset_mismatch of holed offset * holed offset
  | Instruction_mismatch of holed instr * holed instr
  | Instruction_list_mismatch of holed instr list * holed instr list
  | Statement_mismatch of holed stmt * holed stmt
  | Statement_kind_mismatch of holed stmtkind * holed stmtkind
  | Statement_sequence_mismatch of
      holed stmt_seq_item list * holed stmt_seq_item list
  | Init_mismatch of holed init * holed init
  | Fundec_mismatch of holed fundec * holed fundec
  | Global_mismatch of holed global * holed global
  | File_mismatch of holed file * holed file
  | Ast_mismatch of holed ast * holed ast

let ( let* ) = Result.bind

let lift_substitution_error result =
  Result.map_error (fun error -> Substitution_error error) result

let mismatch error = Error error

let require_equal error left right =
  (* equality 문제는 없지만 항상 생각해야 함 *)
  if left = right then Ok () else mismatch error

let rec unify_exp_under substitution left right =
  let require_equal_here left_value right_value =
    require_equal (Expression_mismatch (left, right)) left_value right_value
  in
  if left = right then Ok substitution
  else
    match (left, right) with
    | ExpHole _, _ | _, ExpHole _ ->
        unify_exp_hole substitution left right
    | Const left_const, Const right_const ->
        let* () = require_equal_here left_const right_const in
        Ok substitution
    | Lval left_lval, Lval right_lval ->
        unify_lval_under substitution left_lval right_lval
    | UnOp (left_op, left_exp, left_typ),
      UnOp (right_op, right_exp, right_typ) ->
        let* () =
          require_equal_here
            (left_op, left_typ) (right_op, right_typ)
        in
        unify_exp_under substitution left_exp right_exp
    | BinOp (left_op, left1, left2, left_typ),
      BinOp (right_op, right1, right2, right_typ) ->
        let* () =
          require_equal_here
            (left_op, left_typ) (right_op, right_typ)
        in
        let* substitution = unify_exp_under substitution left1 right1 in
        unify_exp_under substitution left2 right2
    | AddrOf left_lval, AddrOf right_lval
    | StartOf left_lval, StartOf right_lval ->
        unify_lval_under substitution left_lval right_lval
    | _ -> mismatch (Expression_mismatch (left, right))

(* 양쪽이 hole인 경우 *)
and unify_exp_holes substitution left right =
  match
    ( Substitution.find_exp left substitution,
      Substitution.find_exp right substitution )
  with
  | Some left, Some right -> unify_exp_under substitution left right
  | Some left, None -> unify_exp_under substitution left (ExpHole right)
  | None, Some right -> unify_exp_under substitution (ExpHole left) right
  | None, None ->
      if left < right then
        lift_substitution_error
          (Substitution.bind_exp substitution right (ExpHole left))
      else
        lift_substitution_error
          (Substitution.bind_exp substitution left (ExpHole right))

(* 둘 중 하나 이상이 hole인 경우 *)
and unify_exp_hole substitution left right =
  match (left, right) with
  | ExpHole left_hole, ExpHole right_hole ->
      unify_exp_holes substitution left_hole right_hole
  | ExpHole hole, exp | exp, ExpHole hole -> (
      match Substitution.find_exp hole substitution with
      | Some bound -> unify_exp_under substitution bound exp
      | None ->
          lift_substitution_error
            (Substitution.bind_exp substitution hole exp))
  | _ -> mismatch (Expression_mismatch (left, right))

and unify_lval_under substitution left right =
  if left = right then Ok substitution
  else
    let left_host, left_offset = left in
    let right_host, right_offset = right in
    let* substitution =
      unify_lhost_under substitution left_host right_host
    in
    unify_offset_under substitution left_offset right_offset

and unify_lhost_under substitution left right =
  let require_equal_here left_value right_value =
    require_equal (Lhost_mismatch (left, right)) left_value right_value
  in
  if left = right then Ok substitution
  else
    match (left, right) with
    | Var left_var, Var right_var ->
        let* () = require_equal_here left_var right_var in
        Ok substitution
    | Mem left_exp, Mem right_exp ->
        unify_exp_under substitution left_exp right_exp
    | _ -> mismatch (Lhost_mismatch (left, right))

and unify_offset_under substitution left right =
  let require_equal_here left_value right_value =
    require_equal (Offset_mismatch (left, right)) left_value right_value
  in
  if left = right then Ok substitution
  else
    match (left, right) with
    | Field (left_field, left_offset), Field (right_field, right_offset) ->
        let* () = require_equal_here left_field right_field in
        unify_offset_under substitution left_offset right_offset
    | Index (left_exp, left_offset), Index (right_exp, right_offset) ->
        let* substitution =
          unify_exp_under substitution left_exp right_exp
        in
        unify_offset_under substitution left_offset right_offset
    | _ -> mismatch (Offset_mismatch (left, right))

let unify_instr_under substitution left right =
  let mismatch_here = Instruction_mismatch (left, right) in
  let rec unify_arguments substitution left_arguments right_arguments =
    match (left_arguments, right_arguments) with
    | [], [] -> Ok substitution
    | left_exp :: left_rest, right_exp :: right_rest ->
        let* substitution =
          unify_exp_under substitution left_exp right_exp
        in
        unify_arguments substitution left_rest right_rest
    | _ -> mismatch mismatch_here
  in
  if left = right then Ok substitution
  else
    match (left, right) with
    | Set (left_lval, left_exp), Set (right_lval, right_exp) ->
        let* substitution =
          unify_lval_under substitution left_lval right_lval
        in
        unify_exp_under substitution left_exp right_exp
    | Call (left_return, left_callee, left_arguments),
      Call (right_return, right_callee, right_arguments) ->
        let* substitution =
          match (left_return, right_return) with
          | None, None -> Ok substitution
          | Some left_lval, Some right_lval ->
              unify_lval_under substitution left_lval right_lval
          | _ -> mismatch mismatch_here
        in
        let* substitution =
          unify_exp_under substitution left_callee right_callee
        in
        unify_arguments substitution left_arguments right_arguments
    | _ -> mismatch mismatch_here

let unify_instr_list_under substitution left right =
  let mismatch_here = Instruction_list_mismatch (left, right) in
  let rec unify substitution left right =
    match (left, right) with
    | [], [] -> Ok substitution
    | left_instr :: left_rest, right_instr :: right_rest ->
        let* substitution =
          unify_instr_under substitution left_instr right_instr
        in
        unify substitution left_rest right_rest
    | _ -> mismatch mismatch_here
  in
  unify substitution left right

let rec unify_stmt_under substitution left right =
  if left = right then Ok substitution
  else
    let* () =
      require_equal (Statement_mismatch (left, right)) left.labels right.labels
    in
    unify_stmtkind_under substitution left.skind right.skind

and unify_stmtkind_under substitution left right =
  let mismatch_here = Statement_kind_mismatch (left, right) in
  if left = right then Ok substitution
  else
    match (left, right) with
    | Instr left_instrs, Instr right_instrs ->
        unify_instr_list_under substitution left_instrs right_instrs
    | Return None, Return None -> Ok substitution
    | Return (Some left_exp), Return (Some right_exp) ->
        unify_exp_under substitution left_exp right_exp
    | If (left_condition, left_then, left_else),
      If (right_condition, right_then, right_else) ->
        let* substitution =
          unify_exp_under substitution left_condition right_condition
        in
        let* substitution =
          unify_block_under substitution left_then right_then
        in
        unify_block_under substitution left_else right_else
    | Loop left_block, Loop right_block
    | Block left_block, Block right_block ->
        unify_block_under substitution left_block right_block
    | Break, Break | Continue, Continue -> Ok substitution
    | _ -> mismatch mismatch_here

and unify_block_under substitution left right =
  unify_stmt_seq_under substitution left.bstmts right.bstmts

and unify_stmt_seq_under substitution left right =
  let mismatch_here = Statement_sequence_mismatch (left, right) in
  if left = right then Ok substitution
  else
    match (left, right) with
    | Stmt left_stmt :: left_rest, Stmt right_stmt :: right_rest ->
        let* substitution =
          unify_stmt_under substitution left_stmt right_stmt
        in
        unify_stmt_seq_under substitution left_rest right_rest
    | [ StmtSeqHole left_hole ], [ StmtSeqHole right_hole ] ->
        unify_stmt_seq_holes substitution left_hole right_hole
    | [ StmtSeqHole hole ], right
    | right, [ StmtSeqHole hole ] ->
        unify_stmt_seq_hole substitution hole right
    | _ -> mismatch mismatch_here

(* 둘 다 hole *)
and unify_stmt_seq_holes substitution left right =
  match
    ( Substitution.find_stmt_seq left substitution,
      Substitution.find_stmt_seq right substitution )
  with
  | Some left_bound, Some right_bound ->
      unify_stmt_seq_under substitution left_bound right_bound
  | Some left_bound, None ->
      unify_stmt_seq_under substitution left_bound [ StmtSeqHole right ]
  | None, Some right_bound ->
      unify_stmt_seq_under substitution [ StmtSeqHole left ] right_bound
  | None, None ->
      if left = right then Ok substitution
      else if left < right then
        lift_substitution_error
          (Substitution.bind_stmt_seq substitution right [ StmtSeqHole left ])
      else
        lift_substitution_error
          (Substitution.bind_stmt_seq substitution left [ StmtSeqHole right ])

(* 둘 중 하나만 hole *)
and unify_stmt_seq_hole substitution hole stmt_seq =
  match Substitution.find_stmt_seq hole substitution with
  | Some bound -> unify_stmt_seq_under substitution bound stmt_seq
  | None ->
      lift_substitution_error
        (Substitution.bind_stmt_seq substitution hole stmt_seq)

let rec unify_init_under substitution left right =
  let mismatch_here = Init_mismatch (left, right) in
  let rec unify_fields substitution left_fields right_fields =
    match (left_fields, right_fields) with
    | [], [] -> Ok substitution
    | (left_offset, left_init) :: left_rest,
      (right_offset, right_init) :: right_rest ->
        let* substitution =
          unify_offset_under substitution left_offset right_offset
        in
        let* substitution =
          unify_init_under substitution left_init right_init
        in
        unify_fields substitution left_rest right_rest
    | _ -> mismatch mismatch_here
  in
  if left = right then Ok substitution
  else
    match (left, right) with
    | SingleInit left_exp, SingleInit right_exp ->
        unify_exp_under substitution left_exp right_exp
    | CompoundInit (left_typ, left_fields),
      CompoundInit (right_typ, right_fields) ->
        let* () = require_equal mismatch_here left_typ right_typ in
        unify_fields substitution left_fields right_fields
    | _ -> mismatch mismatch_here

let unify_fundec_under substitution left right =
  let mismatch_here = Fundec_mismatch (left, right) in
  if left = right then Ok substitution
  else
    let* () = require_equal mismatch_here left.svar right.svar in
    let* () =
      require_equal mismatch_here left.sformals right.sformals
    in
    let* () = require_equal mismatch_here left.slocals right.slocals in
    unify_block_under substitution left.sbody right.sbody

let unify_global_under substitution left right =
  let mismatch_here = Global_mismatch (left, right) in
  if left = right then Ok substitution
  else
    match (left, right) with
    | GFun left_fundec, GFun right_fundec ->
        unify_fundec_under substitution left_fundec right_fundec
    | GVarDecl left_var, GVarDecl right_var ->
        let* () = require_equal mismatch_here left_var right_var in
        Ok substitution
    | GVar (left_var, left_initinfo), GVar (right_var, right_initinfo) ->
        let* () = require_equal mismatch_here left_var right_var in
        (match (left_initinfo.init, right_initinfo.init) with
        | None, None -> Ok substitution
        | Some left_init, Some right_init ->
            unify_init_under substitution left_init right_init
        | _ -> mismatch mismatch_here)
    | _ -> mismatch mismatch_here

let unify_file_under substitution left right =
  let mismatch_here = File_mismatch (left, right) in
  (* globals 순서까지 일치 *)
  let rec unify_globals substitution left_globals right_globals =
    match (left_globals, right_globals) with
    | [], [] -> Ok substitution
    | left_global :: left_rest, right_global :: right_rest ->
        let* substitution =
          unify_global_under substitution left_global right_global
        in
        unify_globals substitution left_rest right_rest
    | _ -> mismatch mismatch_here
  in
  if left = right then Ok substitution
  else
    let* () = require_equal mismatch_here left.fileName right.fileName in (* 굳이 해야되나 싶긴 함 *)
    unify_globals substitution left.globals right.globals


let unify_ast_under substitution left right =
  if left = right then Ok substitution
  else
    match (left, right) with
    | AExp left_exp, AExp right_exp ->
        unify_exp_under substitution left_exp right_exp
    | ALval left_lval, ALval right_lval ->
        unify_lval_under substitution left_lval right_lval
    | AOffset left_offset, AOffset right_offset ->
        unify_offset_under substitution left_offset right_offset
    | AInstr left_instr, AInstr right_instr ->
        unify_instr_under substitution left_instr right_instr
    | AStmt left_stmt, AStmt right_stmt ->
        unify_stmt_under substitution left_stmt right_stmt
    | ABlock left_block, ABlock right_block ->
        unify_block_under substitution left_block right_block
    | AFundec left_fundec, AFundec right_fundec ->
        unify_fundec_under substitution left_fundec right_fundec
    | AInit left_init, AInit right_init ->
        unify_init_under substitution left_init right_init
    | AGlobal left_global, AGlobal right_global ->
        unify_global_under substitution left_global right_global
    | AFile left_file, AFile right_file ->
        unify_file_under substitution left_file right_file
    | _ -> mismatch (Ast_mismatch (left, right))

let unify_exp left right =
  unify_exp_under Substitution.empty left right

let unify_lval left right =
  unify_lval_under Substitution.empty left right

let unify_offset left right =
  unify_offset_under Substitution.empty left right

let unify_instr left right =
  unify_instr_under Substitution.empty left right

let unify_stmt left right =
  unify_stmt_under Substitution.empty left right

let unify_block left right =
  unify_block_under Substitution.empty left right

let unify_stmt_seq left right =
  unify_stmt_seq_under Substitution.empty left right

let unify_init left right =
  unify_init_under Substitution.empty left right

let unify_fundec left right =
  unify_fundec_under Substitution.empty left right

let unify_global left right =
  unify_global_under Substitution.empty left right

let unify_file left right =
  unify_file_under Substitution.empty left right

let unify_ast left right =
  unify_ast_under Substitution.empty left right

let string_of_ast_kind = function
  | AExp _ -> "expression"
  | ALval _ -> "lvalue"
  | AOffset _ -> "offset"
  | AInstr _ -> "instruction"
  | AStmt _ -> "statement"
  | ABlock _ -> "block"
  | AFundec _ -> "function"
  | AInit _ -> "initializer"
  | AGlobal _ -> "global"
  | AFile _ -> "file"

let string_of_error = function
  | Substitution_error error -> Substitution.string_of_error error
  | Expression_mismatch (left, right) ->
      Printf.sprintf "expression mismatch: %s <> %s"
        (Exp.string_of_t left) (Exp.string_of_t right)
  | Lhost_mismatch (left, right) ->
      Printf.sprintf "lhost mismatch: %s <> %s"
        (Exp.string_of_lhost left) (Exp.string_of_lhost right)
  | Offset_mismatch (left, right) ->
      Printf.sprintf "offset mismatch: %s <> %s"
        (Exp.string_of_offset left) (Exp.string_of_offset right)
  | Instruction_mismatch (left, right) ->
      Printf.sprintf "instruction mismatch: %s <> %s"
        (string_of_instr left) (string_of_instr right)
  | Instruction_list_mismatch (left, right) ->
      let string_of_instrs instrs =
        instrs |> List.map string_of_instr |> String.concat " "
      in
      Printf.sprintf "instruction list mismatch: [%s] <> [%s]"
        (string_of_instrs left) (string_of_instrs right)
  | Statement_mismatch (left, right) ->
      Printf.sprintf "statement mismatch: %s <> %s"
        (string_of_stmt left) (string_of_stmt right)
  | Statement_kind_mismatch (left, right) ->
      Printf.sprintf "statement kind mismatch: %s <> %s"
        (string_of_stmtkind left) (string_of_stmtkind right)
  | Statement_sequence_mismatch (left, right) ->
      Printf.sprintf "statement sequence mismatch: %s <> %s"
        (string_of_block { bstmts = left })
        (string_of_block { bstmts = right })
  | Init_mismatch (left, right) ->
      Printf.sprintf "initializer mismatch: %s <> %s"
        (string_of_init left) (string_of_init right)
  | Fundec_mismatch (left, right) ->
      Printf.sprintf "function mismatch: %s <> %s"
        (string_of_fundec left) (string_of_fundec right)
  | Global_mismatch (left, right) ->
      Printf.sprintf "global mismatch: %s <> %s"
        (string_of_global left) (string_of_global right)
  | File_mismatch (left, right) ->
      Printf.sprintf "file mismatch: %s <> %s"
        (string_of_file left) (string_of_file right)
  | Ast_mismatch (left, right) ->
      Printf.sprintf "AST kind mismatch: %s <> %s"
        (string_of_ast_kind left) (string_of_ast_kind right)
