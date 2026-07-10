type ikind =
  (*
  | IChar
  | ISChar
  | IUChar
  | IBool
  *)
  | IInt
  | IUInt
  (*
  | IShort
  | IUShort
  | ILong
  | IULong
  | ILongLong
  | IULongLong
  | IInt128
  | IUInt128
  *)

type t =
  | TVoid (* CIL: TVoid of attributes *)
  | TInt of ikind (* CIL: TInt of ikind * attributes *)
  (*
  | TFloat of fkind
  *)
  | TPtr of t (* CIL: TPtr of typ * attributes *)
  | TArray of t * int64 option
    (* CIL: TArray of typ * exp option * attributes.
       CIL-- keeps only constant integer array lengths to avoid a Typ/Syntax
       module cycle. *)
  | TFun of t * (string * t) list option
    (* CIL: TFun of typ * (string * typ * attributes) list option
       * bool * attributes. CIL-- does not support varargs. *)
  (*
  | TNamed of typeinfo
  | TComp of compinfo
  | TEnum of enuminfo
  | TBuiltin_va_list
  *)

let string_of_ikind = function
  | IInt -> "int"
  | IUInt -> "unsigned int"

let rec string_of_t = function
  | TVoid -> "void"
  | TInt ikind -> string_of_ikind ikind
  | TPtr typ -> string_of_t typ ^ " *"
  | TArray (typ, None) -> string_of_t typ ^ "[]"
  | TArray (typ, Some _) -> string_of_t typ ^ "[]"
  | TFun (ret, None) -> string_of_t ret ^ "()"
  | TFun (ret, Some []) -> string_of_t ret ^ "(void)"
  | TFun (ret, Some params) ->
      let params =
        params
        |> List.map (fun (name, typ) -> string_of_t typ ^ " " ^ name)
        |> String.concat ", "
      in
      string_of_t ret ^ "(" ^ params ^ ")"
