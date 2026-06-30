type object_id =
  | Global of int
  | Stack of int
  | Heap of int

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
