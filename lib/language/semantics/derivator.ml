module S = Syntax

open BigStep

type error =
  | Value_error of Value.error
  | Memory_error of Memory.error
  | Unsupported of string
  | Type_error of string
  | Missing_main
  | Multiple_main
  | Function_not_found of S.varinfo
  | Arity_mismatch of {
      function_name : string;
      expected : int;
      actual : int;
    }
  | Missing_return of S.fundec
  | Return_value_in_void_function of S.fundec
  | Return_without_value_in_nonvoid_function of S.fundec
  | Break_outside_loop
  | Continue_outside_loop
  | Out_of_fuel

type fuel = int

let default_fuel = 100

let ( let* ) = Result.bind

let map_memory_error = function
  | Ok value -> Ok value
  | Error err -> Error (Memory_error err)

let map_int32_error = function
  | Ok value -> Ok value
  | Error err -> Error (Value_error (Value.Int32_error err))

let unsupported msg = Error (Unsupported msg)
let type_error msg = Error (Type_error msg)

let consume_fuel fuel =
  if fuel <= 0 then Error Out_of_fuel else Ok (fuel - 1)

module FunMap = Map.Make (Memory.VarId)

type context = {
  functions : S.fundec FunMap.t;
}

let function_return_type fd = fd.S.svar.S.vtype

let is_void_type = function
  | Typ.TVoid -> true
  | _ -> false

let build_context file =
  let functions =
    List.fold_left
      (fun functions -> function
        | S.GFun fd -> FunMap.add fd.S.svar.S.vid fd functions
        | S.GVarDecl _ | S.GVar _ -> functions)
      FunMap.empty file.S.globals
  in
  { functions }

let main_functions file =
  List.filter_map
    (function
      | S.GFun fd when String.equal fd.S.svar.S.vname "main" -> Some fd
      | _ -> None)
    file.S.globals

let e_concl = function
  | EConst concl
  | ELval (_, concl)
  | EUnOp (_, concl)
  | ELogicalOrLeftTrue (_, concl)
  | ELogicalOrLeftFalse (_, _, concl)
  | ELogicalAndLeftFalse (_, concl)
  | ELogicalAndLeftTrue (_, _, concl)
  | EBinOp (_, _, concl)
  | EAddrOf (_, concl)
  | EStartOf (_, concl) ->
      concl

let e_value tree =
  let _, _, value = e_concl tree in
  value

let l_concl = function
  | LVar concl | LMem (_, concl) | LIndex (_, _, concl) -> concl

let l_loc tree =
  let _, _, loc = l_concl tree in
  loc

let b_concl = function
  | BEmpty concl
  | BSeqNormal (_, _, concl)
  | BSeqReturn (_, concl)
  | BSeqBreak (_, concl)
  | BSeqContinue (_, concl) ->
      concl

let f_concl = function
  | FReturn (_, concl) | FNoReturn (_, concl) -> concl

let b_output_memory tree =
  let _, _, mem, _ = b_concl tree in
  mem

let b_control tree =
  let _, _, _, control = b_concl tree in
  control

let f_output_memory tree =
  let _, _, _, mem, _ = f_concl tree in
  mem

let f_control tree =
  let _, _, _, _, control = f_concl tree in
  control

let expect_int = function
  | Value.Int n -> Ok n
  | Value.Ptr _ -> type_error "expected integer value"

let value_of_int_result result =
  let* n = map_int32_error result in
  Ok (Value.Int n)

let eval_unop op value =
  match op with
  | S.Neg ->
      let* n = expect_int value in
      value_of_int_result (Value.Int32.neg n)
  | S.LNot ->
      let* b = Value.truthy value in
      Ok (Value.of_bool (not b))
  | S.BNot -> unsupported "bitwise not"

let eval_int_binary f left right =
  let* left = expect_int left in
  let* right = expect_int right in
  value_of_int_result (f left right)

let eval_binop op left right =
  match op with
  | S.PlusA -> eval_int_binary Value.Int32.add left right
  | S.MinusA -> eval_int_binary Value.Int32.sub left right
  | S.Mult -> eval_int_binary Value.Int32.mul left right
  | S.Div -> eval_int_binary Value.Int32.div left right
  | S.Mod -> eval_int_binary Value.Int32.rem left right
  | S.Lt -> eval_int_binary Value.Int32.lt left right
  | S.Gt -> eval_int_binary Value.Int32.gt left right
  | S.Le -> eval_int_binary Value.Int32.le left right
  | S.Ge -> eval_int_binary Value.Int32.ge left right
  | S.Eq -> eval_int_binary Value.Int32.eq left right
  | S.Ne -> eval_int_binary Value.Int32.ne left right
  | S.PlusPI | S.IndexPI | S.MinusPI | S.MinusPP ->
      unsupported "pointer arithmetic"
  | S.Shiftlt | S.Shiftrt -> unsupported "shift operator"
  | S.BAnd | S.BXor | S.BOr -> unsupported "bitwise binary operator"
  | S.LAnd | S.LOr -> type_error "logical operator reached eval_binop"

let rec derive_lval mem (lval : S.lval) =
  match lval with
  | S.Var var, S.NoOffset ->
      let* loc = map_memory_error (Memory.loc_of_var var mem) in
      Ok (LVar (mem, lval, loc))
  | S.Mem exp, _ ->
      let* exp_tree = derive_exp mem exp in
      unsupported
        ("dereference lvalue through "
        ^ Value.string_of_t (e_value exp_tree))
  | _, S.Field _ -> unsupported "field offset"
  | _, S.Index _ -> unsupported "index offset"

and derive_exp mem exp =
  match exp with
  | S.Const (S.CInt (n, ikind)) ->
      let* value = value_of_int_result (Value.Int32.of_int64 ikind n) in
      Ok (EConst (mem, exp, value))
  | S.Lval lval ->
      let* ltree = derive_lval mem lval in
      let* value = map_memory_error (Memory.read (l_loc ltree) mem) in
      Ok (ELval (ltree, (mem, exp, value)))
  | S.UnOp (S.Neg, S.Const (S.CInt (n, ikind)), _) ->
      let* value = value_of_int_result (Value.Int32.of_negated_int64 ikind n) in
      Ok (EConst (mem, exp, value))
  | S.UnOp (op, sub_exp, _) ->
      let* sub_tree = derive_exp mem sub_exp in
      let* value = eval_unop op (e_value sub_tree) in
      Ok (EUnOp (sub_tree, (mem, exp, value)))
  | S.BinOp (S.LOr, left_exp, right_exp, _) ->
      let* left_tree = derive_exp mem left_exp in
      let* left_truthy = Value.truthy (e_value left_tree) in
      if left_truthy then
        Ok (ELogicalOrLeftTrue (left_tree, (mem, exp, Value.of_bool true)))
      else
        let* right_tree = derive_exp mem right_exp in
        let* right_truthy = Value.truthy (e_value right_tree) in
        Ok
          (ELogicalOrLeftFalse
             (left_tree, right_tree, (mem, exp, Value.of_bool right_truthy)))
  | S.BinOp (S.LAnd, left_exp, right_exp, _) ->
      let* left_tree = derive_exp mem left_exp in
      let* left_truthy = Value.truthy (e_value left_tree) in
      if not left_truthy then
        Ok (ELogicalAndLeftFalse (left_tree, (mem, exp, Value.of_bool false)))
      else
        let* right_tree = derive_exp mem right_exp in
        let* right_truthy = Value.truthy (e_value right_tree) in
        Ok
          (ELogicalAndLeftTrue
             (left_tree, right_tree, (mem, exp, Value.of_bool right_truthy)))
  | S.BinOp (op, left_exp, right_exp, _) ->
      let* left_tree = derive_exp mem left_exp in
      let* right_tree = derive_exp mem right_exp in
      let* value = eval_binop op (e_value left_tree) (e_value right_tree) in
      Ok (EBinOp (left_tree, right_tree, (mem, exp, value)))
  | S.AddrOf lval ->
      let* ltree = derive_lval mem lval in
      Ok (EAddrOf (ltree, (mem, exp, Value.ptr (l_loc ltree))))
  | S.StartOf lval ->
      let* ltree = derive_lval mem lval in
      Ok (EStartOf (ltree, (mem, exp, Value.ptr (l_loc ltree))))

let rec derive_args mem = function
  | [] -> Ok ([], [])
  | exp :: exps ->
      let* exp_tree = derive_exp mem exp in
      let* exp_trees, values = derive_args mem exps in
      Ok (exp_tree :: exp_trees, e_value exp_tree :: values)

let resolve_direct_callee ctx callee_exp =
  match callee_exp with
  | S.Lval (S.Var var, S.NoOffset) -> (
      match FunMap.find_opt var.S.vid ctx.functions with
      | Some fd -> Ok (DirectCallee (callee_exp, var, fd), fd)
      | None -> Error (Function_not_found var) )
  | _ -> unsupported "indirect function call"

let rec bind_formals formals args mem =
  match formals, args with
  | [], [] -> Ok mem
  | formal :: formals, arg :: args ->
      let* _, mem = map_memory_error (Memory.bind_local formal arg mem) in
      bind_formals formals args mem
  | [], _ :: _ | _ :: _, [] ->
      type_error "arity mismatch escaped derive_function"

let rec allocate_locals locals mem =
  match locals with
  | [] -> Ok mem
  | local :: locals ->
      let* _, mem = map_memory_error (Memory.allocate_local local mem) in
      allocate_locals locals mem

let rec derive_instr ctx fuel mem instr =
  match instr with
  | S.Set (lval, exp) ->
      let* ltree = derive_lval mem lval in
      let* etree = derive_exp mem exp in
      let* out_mem = map_memory_error (Memory.write (l_loc ltree) (e_value etree) mem) in
      Ok (ISet (ltree, etree, (mem, instr, out_mem)), fuel)
  | S.Call (None, callee_exp, args) ->
      let* callee_tree, fd = resolve_direct_callee ctx callee_exp in
      let* arg_trees, arg_values = derive_args mem args in
      let* ftree, fuel = derive_function ctx fuel mem fd arg_values in
      let out_mem = f_output_memory ftree in
      Ok (ICallVoid (callee_tree, arg_trees, ftree, (mem, instr, out_mem)), fuel)
  | S.Call (Some lval, callee_exp, args) ->
      let* ltree = derive_lval mem lval in
      let* callee_tree, fd = resolve_direct_callee ctx callee_exp in
      let* arg_trees, arg_values = derive_args mem args in
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
        (ICallAssign (ltree, callee_tree, arg_trees, ftree, (mem, instr, out_mem)), fuel)

and derive_instrs ctx fuel mem = function
  | [] -> Ok ([], mem, fuel)
  | instr :: instrs ->
      let* itree, fuel = derive_instr ctx fuel mem instr in
      let _, _, mem = match itree with
        | ISet (_, _, concl)
        | ICallVoid (_, _, _, concl)
        | ICallAssign (_, _, _, _, concl) ->
            concl
      in
      let* itrees, mem, fuel = derive_instrs ctx fuel mem instrs in
      Ok (itree :: itrees, mem, fuel)

and derive_stmt ctx fuel mem stmt =
  let* fuel = consume_fuel fuel in
  match stmt.S.skind with
  | S.Instr instrs ->
      let* itrees, out_mem, fuel = derive_instrs ctx fuel mem instrs in
      Ok (SInstr (itrees, (mem, stmt, out_mem, Normal)), fuel)
  | S.Return None -> Ok (SReturnNone (mem, stmt, mem, ReturnVoid), fuel)
  | S.Return (Some exp) ->
      let* etree = derive_exp mem exp in
      Ok (SReturnSome (etree, (mem, stmt, mem, Return (e_value etree))), fuel)
  | S.If (cond, then_block, else_block) ->
      let* cond_tree = derive_exp mem cond in
      let* cond_truthy = Value.truthy (e_value cond_tree) in
      if cond_truthy then
        let* then_tree, fuel = derive_block ctx fuel mem then_block in
        Ok
          ( SIfTrue
              (cond_tree, then_tree, (mem, stmt, b_output_memory then_tree, b_control then_tree)),
            fuel )
      else
        let* else_tree, fuel = derive_block ctx fuel mem else_block in
        Ok
          ( SIfFalse
              (cond_tree, else_tree, (mem, stmt, b_output_memory else_tree, b_control else_tree)),
            fuel )
  | S.Loop body ->
      let* body_tree, fuel = derive_block ctx fuel mem body in
      let body_mem = b_output_memory body_tree in
      begin
        match b_control body_tree with
        | Normal ->
            let* rest_tree, fuel = derive_stmt ctx fuel body_mem stmt in
            let _, _, out_mem, control =
              match rest_tree with
              | SInstr (_, concl)
              | SReturnNone concl
              | SReturnSome (_, concl)
              | SBreak concl
              | SContinue concl
              | SIfTrue (_, _, concl)
              | SIfFalse (_, _, concl)
              | SLoopRepeat (_, _, concl)
              | SLoopContinue (_, _, concl)
              | SLoopBreak (_, concl)
              | SLoopReturn (_, concl)
              | SBlock (_, concl) ->
                  concl
            in
            Ok (SLoopRepeat (body_tree, rest_tree, (mem, stmt, out_mem, control)), fuel)
        | Continue ->
            let* rest_tree, fuel = derive_stmt ctx fuel body_mem stmt in
            let _, _, out_mem, control =
              match rest_tree with
              | SInstr (_, concl)
              | SReturnNone concl
              | SReturnSome (_, concl)
              | SBreak concl
              | SContinue concl
              | SIfTrue (_, _, concl)
              | SIfFalse (_, _, concl)
              | SLoopRepeat (_, _, concl)
              | SLoopContinue (_, _, concl)
              | SLoopBreak (_, concl)
              | SLoopReturn (_, concl)
              | SBlock (_, concl) ->
                  concl
            in
            Ok
              (SLoopContinue (body_tree, rest_tree, (mem, stmt, out_mem, control)), fuel)
        | Break -> Ok (SLoopBreak (body_tree, (mem, stmt, body_mem, Normal)), fuel)
        | Return _ | ReturnVoid as control ->
            Ok (SLoopReturn (body_tree, (mem, stmt, body_mem, control)), fuel)
      end
  | S.Break -> Ok (SBreak (mem, stmt, mem, Break), fuel)
  | S.Continue -> Ok (SContinue (mem, stmt, mem, Continue), fuel)
  | S.Block block ->
      let* btree, fuel = derive_block ctx fuel mem block in
      Ok (SBlock (btree, (mem, stmt, b_output_memory btree, b_control btree)), fuel)

and derive_block ctx fuel mem block =
  match block.S.bstmts with
  | [] -> Ok (BEmpty (mem, block, mem, Normal), fuel)
  | stmt :: stmts -> (
      let rest_block = { S.bstmts = stmts } in
      let* stree, fuel = derive_stmt ctx fuel mem stmt in
      let _, _, stmt_mem, stmt_control =
        match stree with
        | SInstr (_, concl)
        | SReturnNone concl
        | SReturnSome (_, concl)
        | SBreak concl
        | SContinue concl
        | SIfTrue (_, _, concl)
        | SIfFalse (_, _, concl)
        | SLoopRepeat (_, _, concl)
        | SLoopContinue (_, _, concl)
        | SLoopBreak (_, concl)
        | SLoopReturn (_, concl)
        | SBlock (_, concl) ->
            concl
      in
      match stmt_control with
      | Normal ->
          let* rest_tree, fuel = derive_block ctx fuel stmt_mem rest_block in
          Ok
            ( BSeqNormal
                (stree, rest_tree, (mem, block, b_output_memory rest_tree, b_control rest_tree)),
              fuel )
      | Return _ | ReturnVoid ->
          Ok (BSeqReturn (stree, (mem, block, stmt_mem, stmt_control)), fuel)
      | Break -> Ok (BSeqBreak (stree, (mem, block, stmt_mem, Break)), fuel)
      | Continue -> Ok (BSeqContinue (stree, (mem, block, stmt_mem, Continue)), fuel) )

and derive_function ctx fuel call_mem fd args =
  let expected = List.length fd.S.sformals in
  let actual = List.length args in
  if expected <> actual then
    Error
      (Arity_mismatch { function_name = fd.S.svar.S.vname; expected; actual })
  else
    let mem = Memory.enter_function call_mem in
    let* mem = bind_formals fd.S.sformals args mem in
    let* mem = allocate_locals fd.S.slocals mem in
    let* body_tree, fuel = derive_block ctx fuel mem fd.S.sbody in
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
    let* out_mem = map_memory_error (Memory.leave_function body_mem) in
    let concl = (call_mem, fd, args, out_mem, control) in
    if explicit_return then Ok (FReturn (body_tree, concl), fuel)
    else Ok (FNoReturn (body_tree, concl), fuel)

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
        | Return value -> Ok (PMainReturn (ftree, (file, out_mem, value)))
        | ReturnVoid -> Error (Return_without_value_in_nonvoid_function main)
        | Normal -> Error (Missing_return main)
        | Break -> Error Break_outside_loop
        | Continue -> Error Continue_outside_loop
      end

let string_of_var var = Printf.sprintf "%s#%d" var.S.vname var.S.vid

let string_of_error = function
  | Value_error err -> "value error: " ^ Value.string_of_error err
  | Memory_error err -> "memory error: " ^ Memory.string_of_error err
  | Unsupported msg -> "unsupported CIL' construct: " ^ msg
  | Type_error msg -> "type error: " ^ msg
  | Missing_main -> "missing main function"
  | Multiple_main -> "multiple main functions"
  | Function_not_found var -> "function not found: " ^ string_of_var var
  | Arity_mismatch { function_name; expected; actual } ->
      Printf.sprintf "arity mismatch in %s: expected %d argument(s), got %d"
        function_name expected actual
  | Missing_return fd -> "missing return in " ^ fd.S.svar.S.vname
  | Return_value_in_void_function fd ->
      "return value in void function " ^ fd.S.svar.S.vname
  | Return_without_value_in_nonvoid_function fd ->
      "return without value in non-void function " ^ fd.S.svar.S.vname
  | Break_outside_loop -> "break reached function boundary"
  | Continue_outside_loop -> "continue reached function boundary"
  | Out_of_fuel -> "derivation ran out of fuel"
