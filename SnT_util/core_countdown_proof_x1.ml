open Language

module V = Visualizer

let ensure_dir path = if Sys.file_exists path then () else Sys.mkdir path 0o755
let box text = V.make_box text
let proof premises conclusion = V.build_plain_proof premises (box conclusion)

let body_code = "if (x == 0) break; x = x - 1;"
let loop_code = "loop { if (x == 0) break; x = x - 1; };"

let body0 =
  proof [ box "⋮" ] ("{x |-> 0} |- " ^ body_code ^ " => {x |-> 0}, break")

let loop0 = proof [ body0 ] ("{x |-> 0} |- " ^ loop_code ^ " => {x |-> 0}")

let body1 =
  proof [ box "⋮" ] ("{x |-> 1} |- " ^ body_code ^ " => {x |-> 0}")

let loop1 = proof [ body1; loop0 ] ("{x |-> 1} |- " ^ loop_code ^ " => {x |-> 0}")

let tree =
  proof
    [ box "{} |- x = 1; => {x |-> 1}"; loop1 ]
    ("{} |- x = 1; " ^ loop_code ^ " => {x |-> 0}")

let () =
  ensure_dir "dist";
  ensure_dir "dist/proofs";
  let path = "dist/proofs/manual_countdown_loop_core_x1.svg" in
  V.write_box_svg path tree;
  Printf.printf "Core proof SVG written to %s\n" path
