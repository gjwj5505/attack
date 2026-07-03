type object_id =
  | Global of int
  | Stack of int
  | Heap of int

(* Offsets are concrete linear element offsets within an allocated object.
   CIL' lvalue offsets remain structural in Syntax.offset; lvalue evaluation is
   responsible for lowering them through type/layout information into this
   linear offset.

   This keeps concrete memory and pointer arithmetic simple. If future array or
   struct support needs source-shape/debug information, extend this type with an
   optional structural path instead of replacing the linear offset. The linear
   offset should remain the canonical store key. *)
type t = {
  obj : object_id;
  offset : int;
}

module ObjectId = struct
  type nonrec t = object_id

  let compare = compare
end

module ObjectMap = Map.Make (ObjectId)

module OrderedLoc = struct
  type nonrec t = t

  let compare = compare
end

module LocMap = Map.Make (OrderedLoc)
module LocSet = Set.Make (OrderedLoc)

let string_of_object_id = function
  | Global id -> Printf.sprintf "global%d" id
  | Stack id -> Printf.sprintf "stack%d" id
  | Heap id -> Printf.sprintf "heap%d" id

let string_of_t { obj; offset } =
  Printf.sprintf "%s+%d" (string_of_object_id obj) offset
