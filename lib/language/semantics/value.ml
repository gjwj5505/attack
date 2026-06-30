type int_value = {
  ikind : Typ.ikind;
  bits : Stdlib.Int32.t;
}

module Int32 = struct
  module I = Stdlib.Int32

  (* Runtime integers are 32-bit words tagged with a CIL' integer kind. Int64 is
     used only as a wider intermediate for checked conversion from CIL' integer
     literal payloads, signed-overflow checks, and unsigned interpretation for
     division, remainder, comparison, and printing. Do not convert Int64
     payloads with Int64.to_int32 until the range check succeeds; that
     conversion truncates/wraps instead of reporting overflow. *)
  type t = int_value

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

  type error =
    | Undefined_behavior of ub
    | Binary_operator_type_error of {
        left : Typ.ikind;
        right : Typ.ikind;
      }

  let min_value = I.min_int
  let max_value = I.max_int
  let zero = I.zero
  let one = I.one
  let uint32_modulus = 0x1_0000_0000L
  let uint32_max_as_int64 = 0xFFFF_FFFFL

  let int32_min_as_int64 : int64 = Int64.of_int32 min_value
  let int32_max_as_int64 : int64 = Int64.of_int32 max_value

  let make ikind bits = { ikind; bits }
  let make_iint bits = make Typ.IInt bits
  let make_iuint bits = make Typ.IUInt bits
  let bits n = n.bits

  let signed_to_int64 (n : t) : int64 = Int64.of_int32 (bits n)

  let unsigned_to_int64 (n : t) : int64 =
    let signed = Int64.of_int32 (bits n) in
    if Int64.compare signed 0L >= 0 then signed
    else Int64.add signed uint32_modulus

  let signed_in_range (n : int64) : bool =
    Int64.compare int32_min_as_int64 n <= 0
    && Int64.compare n int32_max_as_int64 <= 0

  let unsigned_in_range (n : int64) : bool =
    Int64.compare 0L n <= 0 && Int64.compare n uint32_max_as_int64 <= 0

  let undefined_behavior ub = Error (Undefined_behavior ub)

  let ensure_same_kind a b =
    if a.ikind = b.ikind then Ok ()
    else Error (Binary_operator_type_error { left = a.ikind; right = b.ikind })

  module Signed = struct
    let of_int64 (n : int64) : (t, error) result =
      if signed_in_range n then Ok (make_iint (Int64.to_int32 n))
      else undefined_behavior (Overflow (Literal n))

    let of_negated_int64 (n : int64) : (t, error) result =
      if Int64.equal n Int64.min_int then
        undefined_behavior (Overflow (Negated_literal n))
      else
        let negated = Int64.neg n in
        if signed_in_range negated then Ok (make_iint (Int64.to_int32 negated))
        else undefined_behavior (Overflow (Negated_literal n))

    let checked_binary (operation : t -> t -> operation)
        (op : int64 -> int64 -> int64) (a : t) (b : t) :
        (t, error) result =
      let r = op (signed_to_int64 a) (signed_to_int64 b) in
      if signed_in_range r then Ok (make_iint (Int64.to_int32 r))
      else undefined_behavior (Overflow (operation a b))

    let neg (n : t) : (t, error) result =
      if I.equal (bits n) min_value then undefined_behavior (Overflow (Neg n))
      else Ok (make_iint (I.neg (bits n)))

    let add a b = checked_binary (fun a b -> Add (a, b)) Int64.add a b
    let sub a b = checked_binary (fun a b -> Sub (a, b)) Int64.sub a b
    let mul a b = checked_binary (fun a b -> Mul (a, b)) Int64.mul a b

    let is_division_overflow a b =
      I.equal (bits a) min_value && I.equal (bits b) I.minus_one

    let div (a : t) (b : t) : (t, error) result =
      if I.equal (bits b) zero then
        undefined_behavior (Division_by_zero (Div (a, b)))
      else if is_division_overflow a b then
        undefined_behavior (Overflow (Div (a, b)))
      else Ok (make_iint (I.div (bits a) (bits b)))

    let rem (a : t) (b : t) : (t, error) result =
      if I.equal (bits b) zero then
        undefined_behavior (Division_by_zero (Rem (a, b)))
      else if is_division_overflow a b then
        undefined_behavior (Overflow (Rem (a, b)))
      else Ok (make_iint (I.rem (bits a) (bits b)))

    let eq a b = I.equal (bits a) (bits b)
    let ne a b = not (eq a b)
    let lt a b = I.compare (bits a) (bits b) < 0
    let le a b = I.compare (bits a) (bits b) <= 0
    let gt a b = I.compare (bits a) (bits b) > 0
    let ge a b = I.compare (bits a) (bits b) >= 0
    let to_string n = I.to_string (bits n)
  end

  module Unsigned = struct
    let of_int64 (n : int64) : (t, error) result =
      if unsigned_in_range n then Ok (make_iuint (Int64.to_int32 n))
      else undefined_behavior (Overflow (Literal n))

    let of_negated_int64 (n : int64) : (t, error) result =
      if Int64.equal n Int64.min_int then
        undefined_behavior (Overflow (Negated_literal n))
      else
        let negated = Int64.neg n in
        of_int64 negated

    let neg n = Ok (make_iuint (I.neg (bits n)))
    let add a b = Ok (make_iuint (I.add (bits a) (bits b)))
    let sub a b = Ok (make_iuint (I.sub (bits a) (bits b)))
    let mul a b = Ok (make_iuint (I.mul (bits a) (bits b)))

    let div (a : t) (b : t) : (t, error) result =
      if I.equal (bits b) zero then
        undefined_behavior (Division_by_zero (Div (a, b)))
      else
        let q = Int64.div (unsigned_to_int64 a) (unsigned_to_int64 b) in
        Ok (make_iuint (Int64.to_int32 q))

    let rem (a : t) (b : t) : (t, error) result =
      if I.equal (bits b) zero then
        undefined_behavior (Division_by_zero (Rem (a, b)))
      else
        let r = Int64.rem (unsigned_to_int64 a) (unsigned_to_int64 b) in
        Ok (make_iuint (Int64.to_int32 r))

    let eq a b = I.equal (bits a) (bits b)
    let ne a b = not (eq a b)
    let lt a b = Int64.compare (unsigned_to_int64 a) (unsigned_to_int64 b) < 0
    let le a b = Int64.compare (unsigned_to_int64 a) (unsigned_to_int64 b) <= 0
    let gt a b = Int64.compare (unsigned_to_int64 a) (unsigned_to_int64 b) > 0
    let ge a b = Int64.compare (unsigned_to_int64 a) (unsigned_to_int64 b) >= 0
    let to_string n = Int64.to_string (unsigned_to_int64 n)
  end

  let of_int64 ikind n =
    match ikind with
    | Typ.IInt -> Signed.of_int64 n
    | Typ.IUInt -> Unsigned.of_int64 n

  let of_negated_int64 ikind n =
    match ikind with
    | Typ.IInt -> Signed.of_negated_int64 n
    | Typ.IUInt -> Unsigned.of_negated_int64 n

  let of_ocaml_bool b = make_iint (if b then one else zero)
  let truthy n = I.compare (bits n) zero <> 0

  let unary f_signed f_unsigned n =
    match n.ikind with
    | Typ.IInt -> f_signed n
    | Typ.IUInt -> f_unsigned n

  let binary f_signed f_unsigned a b =
    match ensure_same_kind a b with
    | Error err -> Error err
    | Ok () -> (
        match a.ikind with
        | Typ.IInt -> f_signed a b
        | Typ.IUInt -> f_unsigned a b )

  let binary_pred f_signed f_unsigned a b =
    match binary f_signed f_unsigned a b with
    | Ok result -> Ok (of_ocaml_bool result)
    | Error err -> Error err

  let neg = unary Signed.neg Unsigned.neg
  let add = binary Signed.add Unsigned.add
  let sub = binary Signed.sub Unsigned.sub
  let mul = binary Signed.mul Unsigned.mul
  let div = binary Signed.div Unsigned.div
  let rem = binary Signed.rem Unsigned.rem
  let eq = binary_pred Signed.eq Unsigned.eq
  let ne = binary_pred Signed.ne Unsigned.ne
  let lt = binary_pred Signed.lt Unsigned.lt
  let le = binary_pred Signed.le Unsigned.le
  let gt = binary_pred Signed.gt Unsigned.gt
  let ge = binary_pred Signed.ge Unsigned.ge

  let to_string n =
    match n.ikind with
    | Typ.IInt -> Signed.to_string n
    | Typ.IUInt -> Unsigned.to_string n ^ "U"
end

type t =
  | Int of int_value
  | Ptr of Location.t

type error =
  | Int32_error of Int32.error

let int n = Int n
let ptr loc = Ptr loc
let of_bool b = Int (Int32.of_ocaml_bool b)

let truthy = function
  | Int n -> Ok (Int32.truthy n)
  | Ptr _ -> Ok true

let string_of_t = function
  | Int n -> Int32.to_string n
  | Ptr loc -> "&" ^ Location.string_of_t loc

let string_of_int_operation = function
  | Int32.Literal n -> Int64.to_string n
  | Int32.Negated_literal n -> "-" ^ Int64.to_string n
  | Int32.Neg n -> "-" ^ Int32.to_string n
  | Int32.Add (a, b) ->
      Printf.sprintf "%s + %s" (Int32.to_string a) (Int32.to_string b)
  | Int32.Sub (a, b) ->
      Printf.sprintf "%s - %s" (Int32.to_string a) (Int32.to_string b)
  | Int32.Mul (a, b) ->
      Printf.sprintf "%s * %s" (Int32.to_string a) (Int32.to_string b)
  | Int32.Div (a, b) ->
      Printf.sprintf "%s / %s" (Int32.to_string a) (Int32.to_string b)
  | Int32.Rem (a, b) ->
      Printf.sprintf "%s %% %s" (Int32.to_string a) (Int32.to_string b)

let string_of_int_ub = function
  | Int32.Overflow operation ->
      "signed integer overflow: " ^ string_of_int_operation operation
  | Int32.Division_by_zero operation ->
      "division by zero: " ^ string_of_int_operation operation

let string_of_int32_error = function
  | Int32.Undefined_behavior ub -> "undefined behavior: " ^ string_of_int_ub ub
  | Int32.Binary_operator_type_error { left; right } ->
      Printf.sprintf "integer binary operator type error: %s vs %s"
        (Typ.string_of_ikind left) (Typ.string_of_ikind right)

let string_of_error = function
  | Int32_error err -> string_of_int32_error err
