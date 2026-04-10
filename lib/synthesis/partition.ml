let partition : int -> int -> int list list = 
  fun n k ->
    let rec partition' n k lim prefix acc =
      if k = 0 then
        if n = 0 then prefix :: acc else acc
      else
        if lim = 0 then acc
        else
          let acc = if lim > n then acc else partition' (n - lim) (k - 1) (n - lim) (lim :: prefix) acc in
          partition' n k (lim - 1) prefix acc
    in
    partition' n k n [] []

let print_partition p =
  let s = p |> List.map string_of_int |> String.concat " " in
  Printf.sprintf "[%s]" s

(* let () = 
  let n = 7 in
  let k = 4 in
  let partitions = partition n k in
  let cnt = List.length partitions in
  Printf.printf "Partitions of %d into %d parts: %d\n" n k cnt;
  List.iter (fun p -> print_endline (print_partition p)) partitions *)