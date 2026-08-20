type t = int

let compare = Int.compare
let equal = Int.equal
let add = ( + )
let sub = ( - )
let is_valid size = size >= 0
let to_string = string_of_int

module Map = Map.Make (Int)
