open Syntax

type 'mode error =
  | Unsupported_type of Typ.t
  | Unsupported_lvalue of 'mode lval
  | Unsupported_expression of 'mode exp
  | Unsupported_unop of unop
  | Unsupported_binop of binop
  | Expected_function of 'mode exp
  | Function_without_parameter_types of 'mode exp
  | Arity_mismatch of {
      expected : int;
      actual : int;
    }
  | Type_mismatch of {
      expected : Typ.t;
      actual : Typ.t;
    }
  | Assigning_void_call_result
  | Return_value_in_void_function
  | Return_without_value_in_nonvoid_function of Typ.t

let ( let* ) = Result.bind

let scalar_type = function
  | Typ.TInt _ as typ -> Ok typ
  | typ -> Error (Unsupported_type typ)

let same_type = ( = )

let check_same_type ~expected ~actual =
  if same_type expected actual then Ok ()
  else Error (Type_mismatch { expected; actual })

let int_type = Typ.TInt Typ.IInt

let check_integer_type = function
  | Typ.TInt _ -> Ok ()
  | typ -> Error (Unsupported_type typ)

let check_unop op ~operand_type ~result_type =
  match op with
  | Neg ->
      let* () = check_integer_type operand_type in
      check_same_type ~expected:operand_type ~actual:result_type
  | LNot ->
      let* () = check_integer_type operand_type in
      check_same_type ~expected:int_type ~actual:result_type
  | BNot -> Error (Unsupported_unop op)

let check_same_integer_operands left_type right_type =
  let* () = check_integer_type left_type in
  let* () = check_integer_type right_type in
  check_same_type ~expected:left_type ~actual:right_type

let check_arithmetic_binop ~left_type ~right_type ~result_type =
  let* () = check_same_integer_operands left_type right_type in
  check_same_type ~expected:left_type ~actual:result_type

let check_predicate_binop ~left_type ~right_type ~result_type =
  let* () = check_same_integer_operands left_type right_type in
  check_same_type ~expected:int_type ~actual:result_type

let check_binop op ~left_type ~right_type ~result_type =
  match op with
  | PlusA | MinusA | Mult | Div | Mod ->
      check_arithmetic_binop ~left_type ~right_type ~result_type
  | Lt | Gt | Le | Ge | Eq | Ne | LAnd | LOr ->
      check_predicate_binop ~left_type ~right_type ~result_type
  | PlusPI | IndexPI | MinusPI | MinusPP | Shiftlt | Shiftrt | BAnd | BXor
  | BOr ->
      Error (Unsupported_binop op)

let rec type_of_lval : type mode. mode lval -> (Typ.t, mode error) result =
 fun ((host, offset) as lval) ->
  match host, offset with
  | Var var, NoOffset ->
      let* typ = scalar_type var.vtype in
      Ok typ
  | Mem _, _ | _, Field _ | _, Index _ -> Error (Unsupported_lvalue lval)

and type_of_exp : type mode. mode exp -> (Typ.t, mode error) result =
 fun exp ->
  match exp with
  | ExpHole _ -> Error (Unsupported_expression exp)
  | Const (CInt (_, ikind)) -> Ok (Typ.TInt ikind)
  | Lval lval -> type_of_lval lval
  | UnOp (op, sub_exp, typ) ->
      let* operand_type = type_of_exp sub_exp in
      let* () = check_unop op ~operand_type ~result_type:typ in
      Ok typ
  | BinOp (op, left, right, typ) ->
      let* left_type = type_of_exp left in
      let* right_type = type_of_exp right in
      let* () =
        check_binop op ~left_type ~right_type ~result_type:typ
      in
      Ok typ
  | AddrOf _ | StartOf _ -> Error (Unsupported_expression exp)

let function_type_of_callee :
    type mode.
    mode exp -> (Typ.t * (string * Typ.t) list, mode error) result =
 fun callee ->
  match callee with
  | Lval (Var var, NoOffset) -> (
      match var.vtype with
      | Typ.TFun (ret, Some params) -> Ok (ret, params)
      | Typ.TFun (_, None) -> Error (Function_without_parameter_types callee)
      | _ -> Error (Expected_function callee) )
  | _ -> Error (Expected_function callee)

let check_assign lval exp =
  let* lhs_type = type_of_lval lval in
  let* rhs_type = type_of_exp exp in
  check_same_type ~expected:lhs_type ~actual:rhs_type

let rec check_args params args =
  match params, args with
  | [], [] -> Ok ()
  | (_, expected) :: params, arg :: args ->
      let* actual = type_of_exp arg in
      let* () = check_same_type ~expected ~actual in
      check_args params args
  | [], _ :: _ | _ :: _, [] ->
      Error
        (Arity_mismatch
           { expected = List.length params; actual = List.length args })

let check_call ~return_target ~callee ~args =
  let* return_type, params = function_type_of_callee callee in
  let expected_arity = List.length params in
  let actual_arity = List.length args in
  if expected_arity <> actual_arity then
    Error (Arity_mismatch { expected = expected_arity; actual = actual_arity })
  else
    let* () = check_args params args in
    match return_target, return_type with
    | None, _ -> Ok ()
    | Some _, Typ.TVoid -> Error Assigning_void_call_result
    | Some lval, _ ->
        let* actual = type_of_lval lval in
        check_same_type ~expected:return_type ~actual

let check_return ~return_type exp =
  match return_type, exp with
  | Typ.TVoid, None -> Ok ()
  | Typ.TVoid, Some _ -> Error Return_value_in_void_function
  | _, None -> Error (Return_without_value_in_nonvoid_function return_type)
  | _, Some exp ->
      let* actual = type_of_exp exp in
      check_same_type ~expected:return_type ~actual

let string_of_error : type mode. mode error -> string = function
  | Unsupported_type typ -> "unsupported type: " ^ Typ.string_of_t typ
  | Unsupported_lvalue lval ->
      "unsupported lvalue: " ^ Syntax.string_of_lval lval
  | Unsupported_expression exp ->
      "unsupported expression: " ^ Syntax.Exp.string_of_t exp
  | Unsupported_unop op ->
      "unsupported unary operator: " ^ Syntax.Exp.string_of_unop op
  | Unsupported_binop op ->
      "unsupported binary operator: " ^ Syntax.Exp.string_of_binop op
  | Expected_function exp ->
      "expected function callee: " ^ Syntax.Exp.string_of_t exp
  | Function_without_parameter_types exp ->
      "function without parameter types: " ^ Syntax.Exp.string_of_t exp
  | Arity_mismatch { expected; actual } ->
      Printf.sprintf "arity mismatch: expected %d argument(s), got %d"
        expected actual
  | Type_mismatch { expected; actual } ->
      Printf.sprintf "type mismatch: expected %s, got %s"
        (Typ.string_of_t expected) (Typ.string_of_t actual)
  | Assigning_void_call_result -> "assigning void call result"
  | Return_value_in_void_function -> "return value in void function"
  | Return_without_value_in_nonvoid_function typ ->
      "return without value in non-void function: " ^ Typ.string_of_t typ
