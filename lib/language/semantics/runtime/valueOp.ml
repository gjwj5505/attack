type error =
  | Value_error of Value.error
  | Unsupported_operator of string
  | Unary_operator_type_error of {
      op : string;
      operand : Value.t;
    }
  | Binary_operator_type_error of {
      op : string;
      left : Value.t;
      right : Value.t;
    }

let lift_value_result = function
  | Ok value -> Ok value
  | Error err -> Error (Value_error err)

let unary_type_error op operand =
  Error (Unary_operator_type_error { op; operand })

let binary_type_error op left right =
  Error (Binary_operator_type_error { op; left; right })

let unsupported_operator op = Error (Unsupported_operator op)

let expect_int_unary op = function
  | Value.Int n -> Ok n
  | operand -> unary_type_error op operand

let expect_int_binary op left right =
  match left, right with
  | Value.Int left, Value.Int right -> Ok (left, right)
  | _ -> binary_type_error op left right

let neg value =
  let ( let* ) = Result.bind in
  let* n = expect_int_unary "-" value in
  lift_value_result (Value.of_int32_result (Value.Int32.neg n))

let lnot value =
  let ( let* ) = Result.bind in
  let* truthy = Value.truthy value in
  Ok (Value.of_bool (not truthy))

let int_binary op f left right =
  let ( let* ) = Result.bind in
  let* left, right = expect_int_binary op left right in
  lift_value_result (Value.of_int32_result (f left right))

let plus_a = int_binary "+" Value.Int32.add
let minus_a = int_binary "-" Value.Int32.sub
let mult = int_binary "*" Value.Int32.mul
let div = int_binary "/" Value.Int32.div
let rem = int_binary "%" Value.Int32.rem
let lt = int_binary "<" Value.Int32.lt
let gt = int_binary ">" Value.Int32.gt
let le = int_binary "<=" Value.Int32.le
let ge = int_binary ">=" Value.Int32.ge
let eq = int_binary "==" Value.Int32.eq
let ne = int_binary "!=" Value.Int32.ne

let eval_unop op value =
  match op with
  | Syntax.Neg -> neg value
  | Syntax.LNot -> lnot value
  | Syntax.BNot -> unsupported_operator "~"

let eval_binop op left right =
  match op with
  | Syntax.PlusA -> plus_a left right
  | Syntax.MinusA -> minus_a left right
  | Syntax.Mult -> mult left right
  | Syntax.Div -> div left right
  | Syntax.Mod -> rem left right
  | Syntax.Lt -> lt left right
  | Syntax.Gt -> gt left right
  | Syntax.Le -> le left right
  | Syntax.Ge -> ge left right
  | Syntax.Eq -> eq left right
  | Syntax.Ne -> ne left right
  | Syntax.PlusPI | Syntax.IndexPI | Syntax.MinusPI | Syntax.MinusPP ->
      unsupported_operator "pointer arithmetic"
  | Syntax.Shiftlt | Syntax.Shiftrt -> unsupported_operator "shift operator"
  | Syntax.BAnd | Syntax.BXor | Syntax.BOr ->
      unsupported_operator "bitwise binary operator"
  | Syntax.LAnd | Syntax.LOr ->
      unsupported_operator "short-circuit logical operator"

let string_of_error = function
  | Value_error err -> Value.string_of_error err
  | Unsupported_operator op -> "unsupported operator: " ^ op
  | Unary_operator_type_error { op; operand } ->
      Printf.sprintf "unary operator type error: %s %s" op
        (Value.string_of_t operand)
  | Binary_operator_type_error { op; left; right } ->
      Printf.sprintf "binary operator type error: %s %s %s"
        (Value.string_of_t left) op (Value.string_of_t right)
