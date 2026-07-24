open BigStep
open BigStepUtil
open Syntax
open SyntaxUtil

type error =
  | Value_error of Value.error
  | Value_op_error of ValueOp.error
  | Memory_error of Memory.error
  | Unsupported of string
  | Type_error of string
  | Missing_main
  | Multiple_main
  | Function_not_found of varinfo
  | Arity_mismatch of {
      function_name : string;
      expected : int;
      actual : int;
    }
  | Missing_return of fundec
  | Return_value_in_void_function of fundec
  | Return_without_value_in_nonvoid_function of fundec
  | Break_outside_loop
  | Continue_outside_loop
  | Out_of_fuel

type fuel = int

let default_fuel = 100

let ( let* ) = Result.bind

let map_memory_error = function
  | Ok value -> Ok value
  | Error err -> Error (Memory_error err)

let map_value_error = function
  | Ok value -> Ok value
  | Error err -> Error (Value_error err)

let map_value_op_error = function
  | Ok value -> Ok value
  | Error err -> Error (Value_op_error err)

let unsupported msg = Error (Unsupported msg)

let consume_fuel fuel =
  if fuel <= 0 then Error Out_of_fuel else Ok (fuel - 1)

module FunMap = Map.Make (VarId)

type context = {
  functions : fundec FunMap.t;
}

let build_context file =
  let functions =
    List.fold_left
      (fun functions -> function
        | GFun fd -> FunMap.add fd.svar.vid fd functions
        | GVarDecl _ | GVar _ -> functions)
      FunMap.empty file.globals
  in
  { functions }

let rec derive_lval mem (lval : lval) =
  match lval with
  | Var var, NoOffset ->
      let* loc = map_memory_error (Memory.loc_of_var var mem) in
      Ok (LTreeVar (mem, lval, loc))
  | Mem exp, _ ->
      let* exp_tree = derive_exp mem exp in
      unsupported
        ("dereference lvalue through "
        ^ Value.string_of_t (e_value exp_tree))
  | _, Field _ -> unsupported "field offset"
  | _, Index _ -> unsupported "index offset"

and derive_exp mem exp =
  match exp with
  | Const c ->
      let* value = map_value_error (Value.of_constant c) in
      Ok (ETreeConst (mem, exp, value))
  | Lval lval ->
      let* ltree = derive_lval mem lval in
      let* value = map_memory_error (Memory.read (l_loc ltree) mem) in
      Ok (ETreeLval (ltree, (mem, exp, value)))
  | UnOp (Neg, Const c, _) ->
      let* value = map_value_error (Value.of_negated_constant c) in
      Ok (ETreeConst (mem, exp, value))
  | UnOp (op, sub_exp, _) ->
      let* sub_tree = derive_exp mem sub_exp in
      let* value =
        map_value_op_error (ValueOp.eval_unop op (e_value sub_tree))
      in
      Ok (ETreeUnOp (sub_tree, (mem, exp, value)))
  | BinOp (LOr, left_exp, right_exp, _) ->
      let* left_tree = derive_exp mem left_exp in
      let* left_truthy = Value.truthy (e_value left_tree) in
      if left_truthy then
        Ok (ETreeLogicalOrLeftTrue (left_tree, (mem, exp, Value.of_bool true)))
      else
        let* right_tree = derive_exp mem right_exp in
        let* right_truthy = Value.truthy (e_value right_tree) in
        Ok
          (ETreeLogicalOrLeftFalse
             (left_tree, right_tree, (mem, exp, Value.of_bool right_truthy)))
  | BinOp (LAnd, left_exp, right_exp, _) ->
      let* left_tree = derive_exp mem left_exp in
      let* left_truthy = Value.truthy (e_value left_tree) in
      if not left_truthy then
        Ok (ETreeLogicalAndLeftFalse (left_tree, (mem, exp, Value.of_bool false)))
      else
        let* right_tree = derive_exp mem right_exp in
        let* right_truthy = Value.truthy (e_value right_tree) in
        Ok
          (ETreeLogicalAndLeftTrue
             (left_tree, right_tree, (mem, exp, Value.of_bool right_truthy)))
  | BinOp (op, left_exp, right_exp, _) ->
      let* left_tree = derive_exp mem left_exp in
      let* right_tree = derive_exp mem right_exp in
      let* value =
        map_value_op_error
          (ValueOp.eval_binop op (e_value left_tree) (e_value right_tree))
      in
      Ok (ETreeBinOp (left_tree, right_tree, (mem, exp, value)))
  | AddrOf lval ->
      let* ltree = derive_lval mem lval in
      Ok (ETreeAddrOf (ltree, (mem, exp, Value.ptr (l_loc ltree))))
  | StartOf lval ->
      let* ltree = derive_lval mem lval in
      Ok (ETreeStartOf (ltree, (mem, exp, Value.ptr (l_loc ltree))))

let rec derive_args mem = function
  | [] -> Ok []
  | exp :: exps ->
      let* exp_tree = derive_exp mem exp in
      let* exp_trees = derive_args mem exps in
      Ok (exp_tree :: exp_trees)

let resolve_direct_callee ctx callee_exp =
  match callee_exp with
  | Lval (Var var, NoOffset) -> (
      match FunMap.find_opt var.vid ctx.functions with
      | Some fd -> Ok (CalleeTreeDirect (callee_exp, var, fd))
      | None -> Error (Function_not_found var) )
  | _ -> unsupported "indirect function call"

let rec bind_formals formals args mem =
  match formals, args with
  | [], [] -> Ok mem
  | formal :: formals, arg :: args ->
      let* _, mem = map_memory_error (Memory.bind_local formal arg mem) in
      bind_formals formals args mem
  | [], _ :: _ | _ :: _, [] ->
      Error (Type_error "arity mismatch escaped derive_function")

let rec allocate_locals locals mem =
  match locals with
  | [] -> Ok mem
  | local :: locals ->
      let* _, mem = map_memory_error (Memory.allocate_local local mem) in
      allocate_locals locals mem

let rec derive_instr ctx fuel mem instr =
  let* fuel = consume_fuel fuel in
  match instr with
  | Set (lval, exp) ->
      let* ltree = derive_lval mem lval in
      let* etree = derive_exp mem exp in
      let* out_mem = map_memory_error (Memory.write (l_loc ltree) (e_value etree) mem) in
      Ok (ITreeSet (ltree, etree, (mem, instr, out_mem)), fuel)
  | Call (None, callee_exp, args) ->
      let* callee_tree = resolve_direct_callee ctx callee_exp in
      let fd = callee_fundec callee_tree in
      let* arg_trees = derive_args mem args in
      let arg_values = List.map e_value arg_trees in
      let* ftree, fuel = derive_function ctx fuel mem fd arg_values in
      let out_mem = f_output_memory ftree in
      Ok (ITreeCallVoid (callee_tree, arg_trees, ftree, (mem, instr, out_mem)), fuel)
  | Call (Some lval, callee_exp, args) ->
      let* ltree = derive_lval mem lval in
      let* callee_tree = resolve_direct_callee ctx callee_exp in
      let fd = callee_fundec callee_tree in
      let* arg_trees = derive_args mem args in
      let arg_values = List.map e_value arg_trees in
      let* ftree, fuel = derive_function ctx fuel mem fd arg_values in
      let callee_out_mem = f_output_memory ftree in
      let* value =
        match f_control ftree with
        | Return value -> Ok value
        | ReturnVoid -> Error (Return_without_value_in_nonvoid_function fd)
        | Normal -> Error (Missing_return fd)
        | Break -> Error Break_outside_loop
        | Continue -> Error Continue_outside_loop
      in
      let* out_mem =
        map_memory_error (Memory.write (l_loc ltree) value callee_out_mem)
      in
      Ok
        (ITreeCallAssign (ltree, callee_tree, arg_trees, ftree, (mem, instr, out_mem)), fuel)

and derive_instrs ctx fuel mem = function
  | [] -> Ok ([], fuel)
  | instr :: instrs ->
      let* itree, fuel = derive_instr ctx fuel mem instr in
      let mem = i_output_memory itree in
      let* itrees, fuel = derive_instrs ctx fuel mem instrs in
      Ok (itree :: itrees, fuel)

and derive_stmt ctx fuel mem stmt =
  match stmt.skind with
  | Instr instrs ->
      let* itrees, fuel = derive_instrs ctx fuel mem instrs in
      let out_mem = instrs_output_memory mem itrees in
      Ok (STreeInstr (itrees, (mem, stmt, out_mem, Normal)), fuel)
  | skind ->
      let* fuel = consume_fuel fuel in
      match skind with
      | Syntax.Return None ->
          Ok (STreeReturnNone (mem, stmt, mem, ReturnVoid), fuel)
      | Syntax.Return (Some exp) ->
          let* etree = derive_exp mem exp in
          Ok
            (STreeReturnSome (etree, (mem, stmt, mem, Return (e_value etree))), fuel)
      | If (cond, then_block, else_block) ->
          let* cond_tree = derive_exp mem cond in
          let* cond_truthy = Value.truthy (e_value cond_tree) in
          if cond_truthy then
            let* then_tree, fuel = derive_block ctx fuel mem then_block in
            Ok
              ( STreeIfTrue
                  ( cond_tree,
                    then_tree,
                    (mem, stmt, b_output_memory then_tree, b_control then_tree)
                  ),
                fuel )
          else
            let* else_tree, fuel = derive_block ctx fuel mem else_block in
            Ok
              ( STreeIfFalse
                  ( cond_tree,
                    else_tree,
                    (mem, stmt, b_output_memory else_tree, b_control else_tree)
                  ),
                fuel )
      | Loop body ->
          let* body_tree, fuel = derive_block ctx fuel mem body in
          let body_mem = b_output_memory body_tree in
          begin
            match b_control body_tree with
            | Normal ->
                let* rest_tree, fuel = derive_stmt ctx fuel body_mem stmt in
                let out_mem = s_output_memory rest_tree in
                let control = s_control rest_tree in
                Ok
                  (STreeLoopRepeat
                     (body_tree, rest_tree, (mem, stmt, out_mem, control)), fuel)
            | Continue ->
                let* rest_tree, fuel = derive_stmt ctx fuel body_mem stmt in
                let out_mem = s_output_memory rest_tree in
                let control = s_control rest_tree in
                Ok
                  (STreeLoopContinue
                     (body_tree, rest_tree, (mem, stmt, out_mem, control)), fuel)
            | Break ->
                Ok (STreeLoopBreak (body_tree, (mem, stmt, body_mem, Normal)), fuel)
            | Return _ | ReturnVoid as control ->
                Ok
                  (STreeLoopReturn (body_tree, (mem, stmt, body_mem, control)), fuel)
          end
      | Syntax.Break -> Ok (STreeBreak (mem, stmt, mem, Break), fuel)
      | Syntax.Continue -> Ok (STreeContinue (mem, stmt, mem, Continue), fuel)
      | Block block ->
          let* btree, fuel = derive_block ctx fuel mem block in
          Ok
            (STreeBlock
               (btree, (mem, stmt, b_output_memory btree, b_control btree)), fuel)
      | Instr _ -> assert false

and derive_block ctx fuel mem block =
  let rec loop rev_strees fuel current_mem = function
    | [] ->
        Ok (BTreeSeq (List.rev rev_strees, (mem, block, current_mem, Normal)), fuel)
    | stmt :: stmts ->
        let* stree, fuel = derive_stmt ctx fuel current_mem stmt in
        let stmt_mem = s_output_memory stree in
        let stmt_control = s_control stree in
        let rev_strees = stree :: rev_strees in
        match stmt_control with
        | Normal -> loop rev_strees fuel stmt_mem stmts
        | Return _ | ReturnVoid | Break | Continue ->
            Ok
              ( BTreeSeq
                  (List.rev rev_strees, (mem, block, stmt_mem, stmt_control)),
                fuel )
  in
  loop [] fuel mem block.bstmts

and derive_function ctx fuel call_mem fd arg_values =
  let expected = List.length fd.sformals in
  let actual = List.length arg_values in
  if expected <> actual then
    Error
      (Arity_mismatch { function_name = var_name fd.svar; expected; actual })
  else
    let mem = Memory.enter_function call_mem in
    let* mem = bind_formals fd.sformals arg_values mem in
    let* mem = allocate_locals fd.slocals mem in
    let* body_tree, fuel = derive_block ctx fuel mem fd.sbody in
    let body_mem = b_output_memory body_tree in
    let body_control = b_control body_tree in
    let* control, explicit_return =
      match function_return_type fd with
      | Typ.TVoid -> (
          match body_control with
          | Normal -> Ok (ReturnVoid, false)
          | ReturnVoid -> Ok (ReturnVoid, true)
          | Return _ -> Error (Return_value_in_void_function fd)
          | Break -> Error Break_outside_loop
          | Continue -> Error Continue_outside_loop )
      | Typ.TInt _ | Typ.TPtr _ | Typ.TArray _ | Typ.TFun _ -> (
          match body_control with
          | Return value -> Ok (Return value, true)
          | ReturnVoid -> Error (Return_without_value_in_nonvoid_function fd)
          | Normal -> Error (Missing_return fd)
          | Break -> Error Break_outside_loop
          | Continue -> Error Continue_outside_loop )
    in
    let* out_mem =
      map_memory_error
        (Memory.leave_function ~caller_stack:call_mem.Memory.stack body_mem)
    in
    let concl = (call_mem, fd, arg_values, out_mem, control) in
    if explicit_return then Ok (FTreeReturn (body_tree, concl), fuel)
    else Ok (FTreeNoReturn (body_tree, concl), fuel)

let derive_file ?(fuel = default_fuel) file =
  let ctx = build_context file in
  match main_functions file with
  | [] -> Error Missing_main
  | _ :: _ :: _ -> Error Multiple_main
  | [ main ] ->
      let* ftree, _fuel = derive_function ctx fuel Memory.empty main [] in
      let out_mem = f_output_memory ftree in
      begin
        match f_control ftree with
        | Return value -> Ok (PTreeMainReturn (ftree, (file, out_mem, value)))
        | ReturnVoid -> Error (Return_without_value_in_nonvoid_function main)
        | Normal -> Error (Missing_return main)
        | Break -> Error Break_outside_loop
        | Continue -> Error Continue_outside_loop
      end

let string_of_error = function
  | Value_error err -> "value error: " ^ Value.string_of_error err
  | Value_op_error err -> "value operator error: " ^ ValueOp.string_of_error err
  | Memory_error err -> "memory error: " ^ Memory.string_of_error err
  | Unsupported msg -> "unsupported CIL-- construct: " ^ msg
  | Type_error msg -> "type error: " ^ msg
  | Missing_main -> "missing main function"
  | Multiple_main -> "multiple main functions"
  | Function_not_found var -> "function not found: " ^ string_of_var var
  | Arity_mismatch { function_name; expected; actual } ->
      Printf.sprintf "arity mismatch in %s: expected %d argument(s), got %d"
        function_name expected actual
  | Missing_return fd -> "missing return in " ^ var_name fd.svar
  | Return_value_in_void_function fd ->
      "return value in void function " ^ var_name fd.svar
  | Return_without_value_in_nonvoid_function fd ->
      "return without value in non-void function " ^ var_name fd.svar
  | Break_outside_loop -> "break reached function boundary"
  | Continue_outside_loop -> "continue reached function boundary"
  | Out_of_fuel -> "derivation ran out of fuel"
