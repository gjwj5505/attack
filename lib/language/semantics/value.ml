module Int = struct
  type t = Int32.t

  type operation =
    | Literal of int64
    | Negated_literal of int64
    | Neg of t
    | Add of t * t
    | Sub of t * t
    | Mul of t * t
    | Div of t * t
    | Rem of t * t

  type ub =
    | Overflow of operation
    | Division_by_zero of operation

  let min_value = Int32.min_int
  let max_value = Int32.max_int
  let zero = Int32.zero
  let one = Int32.one

  let int32_min_as_int64 : int64 = Int64.of_int32 min_value
  let int32_max_as_int64 : int64 = Int64.of_int32 max_value

  let to_int64 (n : t) : int64 = Int64.of_int32 n
  let to_string = Int32.to_string

  let in_range (n : int64) : bool =
    Int64.compare int32_min_as_int64 n <= 0
    && Int64.compare n int32_max_as_int64 <= 0

  let of_int64 (n : int64) : (t, ub) result =
    if in_range n then Ok (Int64.to_int32 n) else Error (Overflow (Literal n))

  let of_negated_int64 (n : int64) : (t, ub) result =
    if Int64.equal n Int64.min_int then
      Error (Overflow (Negated_literal n))
    else
      let negated = Int64.neg n in
      if in_range negated then Ok (Int64.to_int32 negated)
      else Error (Overflow (Negated_literal n))

  let bool b = if b then one else zero
  let truthy n = Int32.compare n zero <> 0

  let neg (n : t) : (t, ub) result =
    if Int32.equal n min_value then Error (Overflow (Neg n))
    else Ok (Int32.neg n)

  let checked_binary (operation : t -> t -> operation)
      (op : int64 -> int64 -> int64) (a : t) (b : t) :
      (t, ub) result =
    let r = op (to_int64 a) (to_int64 b) in
    if in_range r then Ok (Int64.to_int32 r)
    else Error (Overflow (operation a b))

  let add a b = checked_binary (fun a b -> Add (a, b)) Int64.add a b
  let sub a b = checked_binary (fun a b -> Sub (a, b)) Int64.sub a b
  let mul a b = checked_binary (fun a b -> Mul (a, b)) Int64.mul a b

  let is_division_overflow a b =
    Int32.equal a min_value && Int32.equal b Int32.minus_one

  let div (a : t) (b : t) : (t, ub) result =
    if Int32.equal b zero then Error (Division_by_zero (Div (a, b)))
    else if is_division_overflow a b then Error (Overflow (Div (a, b)))
    else Ok (Int32.div a b)

  let rem (a : t) (b : t) : (t, ub) result =
    if Int32.equal b zero then Error (Division_by_zero (Rem (a, b)))
    else if is_division_overflow a b then Error (Overflow (Rem (a, b)))
    else Ok (Int32.rem a b)

  let eq = Int32.equal
  let ne a b = not (eq a b)
  let lt a b = Int32.compare a b < 0
  let le a b = Int32.compare a b <= 0
  let gt a b = Int32.compare a b > 0
  let ge a b = Int32.compare a b >= 0
end

type t =
  | Int of Int.t

type ub =
  | Int_ub of Int.ub

let of_int n = Int n

let string_of_t = function
  | Int n -> Int.to_string n

let string_of_int_operation = function
  | Int.Literal n -> Int64.to_string n
  | Int.Negated_literal n -> "-" ^ Int64.to_string n
  | Int.Neg n -> "-" ^ Int.to_string n
  | Int.Add (a, b) -> Printf.sprintf "%s + %s" (Int.to_string a) (Int.to_string b)
  | Int.Sub (a, b) -> Printf.sprintf "%s - %s" (Int.to_string a) (Int.to_string b)
  | Int.Mul (a, b) -> Printf.sprintf "%s * %s" (Int.to_string a) (Int.to_string b)
  | Int.Div (a, b) -> Printf.sprintf "%s / %s" (Int.to_string a) (Int.to_string b)
  | Int.Rem (a, b) -> Printf.sprintf "%s %% %s" (Int.to_string a) (Int.to_string b)

let string_of_int_ub = function
  | Int.Overflow operation ->
      "signed integer overflow: " ^ string_of_int_operation operation
  | Int.Division_by_zero operation ->
      "division by zero: " ^ string_of_int_operation operation

let string_of_ub = function
  | Int_ub ub -> string_of_int_ub ub
