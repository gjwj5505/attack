open BigStep
open Syntax

type error =
  | Value_ub of Value.ub
  | Memory_error of Memory.error
  | Type_error of string
  | Missing_return
  | Break_outside_loop
  | Continue_outside_loop
  | Out_of_fuel

type fuel = int

let default_fuel = 100

let ( let* ) = Result.bind

let map_int_ub = function
  | Ok value -> Ok value
  | Error ub -> Error (Value_ub (Value.Int_ub ub))

let map_memory_error = function
  | Ok value -> Ok value
  | Error err -> Error (Memory_error err)

let expect_int = function
  | Value.Int n -> Ok n

let value_of_int_result result =
  let* n = map_int_ub result in
  Ok (Value.of_int n)

let eval_uop op value =
  match op with
  | Exp.Uminus ->
      let* n = expect_int value in
      value_of_int_result (Value.Int.neg n)

let eval_int_arith f left right =
  let* left = expect_int left in
  let* right = expect_int right in
  value_of_int_result (f left right)

let eval_int_cmp cmp left right =
  let* left = expect_int left in
  let* right = expect_int right in
  Ok (Value.of_int (Value.Int.bool (cmp left right)))

let eval_plus = eval_int_arith Value.Int.add
let eval_minus = eval_int_arith Value.Int.sub
let eval_times = eval_int_arith Value.Int.mul
let eval_div = eval_int_arith Value.Int.div
let eval_mod = eval_int_arith Value.Int.rem
let eval_eq = eval_int_cmp Value.Int.eq
let eval_ne = eval_int_cmp Value.Int.ne
let eval_lt = eval_int_cmp Value.Int.lt
let eval_le = eval_int_cmp Value.Int.le
let eval_gt = eval_int_cmp Value.Int.gt
let eval_ge = eval_int_cmp Value.Int.ge

let eval_bop op left right =
  let open Exp in
  match op with
  | Plus -> eval_plus left right
  | Minus -> eval_minus left right
  | Times -> eval_times left right
  | Div -> eval_div left right
  | Mod -> eval_mod left right
  | Eq -> eval_eq left right
  | Ne -> eval_ne left right
  | Lt -> eval_lt left right
  | Le -> eval_le left right
  | Gt -> eval_gt left right
  | Ge -> eval_ge left right

let truthy value =
  match value with
  | Value.Int n -> Ok (Value.Int.truthy n)

let consume_fuel fuel =
  if fuel <= 0 then Error Out_of_fuel else Ok (fuel - 1)

let rec derive_exp mem exp =
  match exp with
  | Exp.Int n ->
      let* value = value_of_int_result (Value.Int.of_int64 n) in
      Ok (EIntLiteral ((), (mem, exp, mem, value)))
  | Exp.Lval lval ->
      let* value = map_memory_error (Memory.read_lval lval mem) in
      Ok (ELval ((), (mem, exp, mem, value)))
  | Exp.Uop (Exp.Uminus, Exp.Int n) ->
      let* value = value_of_int_result (Value.Int.of_negated_int64 n) in
      Ok (ENegIntLiteral ((), (mem, exp, mem, value)))
  | Exp.Uop (op, sub_exp) ->
      let* sub_tree = derive_exp mem sub_exp in
      let _, _, sub_mem, sub_value = BigStepUtil.get_e_concl sub_tree in
      let* value = eval_uop op sub_value in
      Ok (EUop (sub_tree, (mem, exp, sub_mem, value)))
  | Exp.Bop (op, left_exp, right_exp) ->
      let* left_tree = derive_exp mem left_exp in
      let _, _, left_mem, left_value = BigStepUtil.get_e_concl left_tree in
      let* right_tree = derive_exp left_mem right_exp in
      let _, _, right_mem, right_value = BigStepUtil.get_e_concl right_tree in
      let* value = eval_bop op left_value right_value in
      Ok (EBop ((left_tree, right_tree), (mem, exp, right_mem, value)))

and derive_stmt fuel mem stmt =
  let* fuel = consume_fuel fuel in
  match stmt with
  | Stmt.Decl (binding, exp) ->
      let* exp_tree = derive_exp mem exp in
      let _, _, exp_mem, value = BigStepUtil.get_e_concl exp_tree in
      let* out_mem = map_memory_error (Memory.declare binding value exp_mem) in
      Ok (SDecl (exp_tree, (mem, stmt, out_mem, Normal)), fuel)
  | Stmt.Assign (lval, exp) ->
      let* exp_tree = derive_exp mem exp in
      let _, _, exp_mem, value = BigStepUtil.get_e_concl exp_tree in
      let* out_mem = map_memory_error (Memory.assign_lval lval value exp_mem) in
      Ok (SAssign (exp_tree, (mem, stmt, out_mem, Normal)), fuel)
  | Stmt.If (cond, then_block, else_block) ->
      let* cond_tree = derive_exp mem cond in
      let _, _, cond_mem, cond_value = BigStepUtil.get_e_concl cond_tree in
      let* cond_truthy = truthy cond_value in
      if cond_truthy then
      let* then_tree, fuel = derive_block fuel cond_mem then_block in
        let b_concl = BigStepUtil.get_b_concl then_tree in
        let out_mem = BigStepUtil.get_b_concl_output_memory b_concl in
        let control = BigStepUtil.get_b_concl_control b_concl in
        Ok (SIfTrue ((cond_tree, then_tree), (mem, stmt, out_mem, control)), fuel)
      else
        let* else_tree, fuel = derive_block fuel cond_mem else_block in
        let b_concl = BigStepUtil.get_b_concl else_tree in
        let out_mem = BigStepUtil.get_b_concl_output_memory b_concl in
        let control = BigStepUtil.get_b_concl_control b_concl in
        Ok (SIfFalse ((cond_tree, else_tree), (mem, stmt, out_mem, control)), fuel)
  | Stmt.While (cond, body) ->
      derive_while fuel mem stmt cond body
  | Stmt.Return exp ->
      let* exp_tree = derive_exp mem exp in
      let _, _, out_mem, value = BigStepUtil.get_e_concl exp_tree in
      Ok (SReturn (exp_tree, (mem, stmt, out_mem, Return value)), fuel)

and derive_while fuel mem stmt cond body =
  let* cond_tree = derive_exp mem cond in
  let _, _, cond_mem, cond_value = BigStepUtil.get_e_concl cond_tree in
  let* cond_truthy = truthy cond_value in
  if not cond_truthy then
    Ok (SWhileFalse (cond_tree, (mem, stmt, cond_mem, Normal)), fuel)
  else
    let* body_tree, fuel = derive_block fuel cond_mem body in
    let body_concl = BigStepUtil.get_b_concl body_tree in
    let body_mem = BigStepUtil.get_b_concl_output_memory body_concl in
    match BigStepUtil.get_b_concl_control body_concl with
    | Normal ->
        let* rest_tree, fuel = derive_stmt fuel body_mem stmt in
        let _, _, out_mem, control = BigStepUtil.get_s_concl rest_tree in
        Ok
          ( SWhileTrueNormal
              ((cond_tree, body_tree, rest_tree), (mem, stmt, out_mem, control)),
            fuel )
    | Continue ->
        let* rest_tree, fuel = derive_stmt fuel body_mem stmt in
        let _, _, out_mem, control = BigStepUtil.get_s_concl rest_tree in
        Ok
          ( SWhileTrueContinue
              ((cond_tree, body_tree, rest_tree), (mem, stmt, out_mem, control)),
            fuel )
    | Break ->
        Ok (SWhileTrueBreak ((cond_tree, body_tree), (mem, stmt, body_mem, Normal)), fuel)
    | Return value ->
        Ok
          ( SWhileTrueReturn
              ((cond_tree, body_tree), (mem, stmt, body_mem, Return value)),
            fuel )

and derive_block fuel mem block =
  match block with
  | [] -> Ok (BEmpty (mem, block, mem, Normal), fuel)
  | stmt :: rest -> (
      let* stmt_tree, fuel = derive_stmt fuel mem stmt in
      let stmt_concl = BigStepUtil.get_s_concl stmt_tree in
      let stmt_mem = BigStepUtil.get_s_concl_output_memory stmt_concl in
      match BigStepUtil.get_s_concl_control stmt_concl with
      | Normal ->
          let* rest_tree, fuel = derive_block fuel stmt_mem rest in
          let _, _, out_mem, control = BigStepUtil.get_b_concl rest_tree in
          Ok
            ( BSeqNormal
                ((stmt_tree, rest_tree), (mem, block, out_mem, control)),
              fuel )
      | Return value ->
          Ok (BSeqReturn (stmt_tree, (mem, block, stmt_mem, Return value)), fuel)
      | Break ->
          Ok (BSeqBreak (stmt_tree, (mem, block, stmt_mem, Break)), fuel)
      | Continue ->
          Ok (BSeqContinue (stmt_tree, (mem, block, stmt_mem, Continue)), fuel) )

let derive_program ?(fuel = default_fuel) ({ main } as program) =
  let mem = Memory.empty |> Memory.enter_function in
  let* body_tree, _fuel = derive_block fuel mem main.body in
  let body_concl = BigStepUtil.get_b_concl body_tree in
  let out_mem = BigStepUtil.get_b_concl_output_memory body_concl in
  match BigStepUtil.get_b_concl_control body_concl with
  | Return value -> Ok (PMainReturn (body_tree, (program, out_mem, value)))
  | Normal -> Error Missing_return
  | Break -> Error Break_outside_loop
  | Continue -> Error Continue_outside_loop

let string_of_error = function
  | Value_ub ub -> "undefined behavior: " ^ Value.string_of_ub ub
  | Memory_error err -> "memory error: " ^ Memory.string_of_error err
  | Type_error msg -> "type error: " ^ msg
  | Missing_return -> "main did not return a value"
  | Break_outside_loop -> "break reached program boundary"
  | Continue_outside_loop -> "continue reached program boundary"
  | Out_of_fuel -> "derivation ran out of fuel"
