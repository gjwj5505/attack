open Language

module V = Visualizer

let ensure_dir path = if Sys.file_exists path then () else Sys.mkdir path 0o755
let box text = V.make_box text
let proof premises conclusion = V.build_plain_proof premises (box conclusion)
let leaf conclusion = proof [ box "⋮" ] conclusion

let unknown_x = "{x |-> ?}"
let after_x = "{x |-> 1}"
let before_y = "{x |-> ?}"
let after_y = "{x |-> ?, y |-> ? + 1}"
let after_seq = "{x |-> 1, y |-> 2}"

let x_assign =
  proof [] ("{} |- x = 1; => " ^ after_x)

let y_assign =
  proof
    [ leaf (unknown_x ^ " |- x => ?"); leaf "? + 1 => ? + 1" ]
    (before_y ^ " |- y = x + 1; => " ^ after_y)

let seq =
  proof
    [
      proof [] ("{} |- x = 1; => " ^ after_x);
      proof
        [ leaf "{x |-> 1} |- x => 1"; leaf "1 + 1 => 2" ]
        ("{x |-> 1} |- y = x + 1; => " ^ after_seq);
    ]
    ("{} |- x = 1; y = x + 1; => " ^ after_seq)

let write name tree =
  ensure_dir "dist";
  ensure_dir "dist/proofs";
  let path = Filename.concat "dist/proofs" name in
  V.write_box_svg path tree;
  Printf.printf "Core proof SVG written to %s\n" path

let () =
  write "core_x_assign.svg" x_assign;
  write "core_y_assign.svg" y_assign;
  write "core_sequence_xy.svg" seq
