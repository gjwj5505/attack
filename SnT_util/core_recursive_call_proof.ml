open Language

module V = Visualizer

let ensure_dir path = if Sys.file_exists path then () else Sys.mkdir path 0o755
let box text = V.make_box text
let proof premises conclusion = V.build_plain_proof premises (box conclusion)
let leaf conclusion = proof [ box "..." ] conclusion

let center_line width text =
  let text_box = box text in
  let left = (width - text_box.V.width) / 2 in
  let right = width - text_box.V.width - left in
  String.make left ' ' ^ text ^ String.make right ' '

let with_bottom_ellipsis tree =
  {
    V.lines =
      tree.V.lines @ [ String.make tree.V.width '-'; center_line tree.V.width "..." ];
    width = tree.V.width;
    height = tree.V.height + 2;
  }

let body_code = "if (x == 0) return 0; return f(x - 1);"
let stack0 = "{x |-> 0 | x |-> 1 | x |-> 2}"

let body0 =
  proof
    [
      proof
        [ box (stack0 ^ " |- x => 0"); box (stack0 ^ " |- 0 == 0 => true") ]
        (stack0 ^ " |- x == 0 => true");
    ]
    (stack0 ^ " |- " ^ body_code ^ " => return 0")

let call0 =
  proof [ body0 ] ("{x |-> 1 | x |-> 2} |- f(0) => 0")

let call0_subtree = with_bottom_ellipsis call0

let body0_top =
  proof
    [
      proof
        [ box "{x |-> 0} |- x => 0"; box "{x |-> 0} |- 0 == 0 => true" ]
        "{x |-> 0} |- x == 0 => true";
    ]
    ("{x |-> 0} |- " ^ body_code ^ " => return 0")

let call0_subtree_top =
  proof [ body0_top ] "{x |-> 1} |- f(0) => 0"
  |> with_bottom_ellipsis

let body1 =
  proof
    [
      leaf "{x |-> 1 | x |-> 2} |- x == 0 => false";
      leaf "{x |-> 1 | x |-> 2} |- x - 1 => 0";
      call0;
    ]
    ("{x |-> 1 | x |-> 2} |- " ^ body_code ^ " => 0")

let call1 =
  proof [ body1 ] ("{x |-> 2} |- f(1) => 0")

let body2 =
  proof
    [
      leaf "{x |-> 2} |- x == 0 => false";
      leaf "{x |-> 2} |- x - 1 => 1";
      call1;
    ]
    ("{x |-> 2} |- " ^ body_code ^ " => 0")

let tree =
  proof [ body2 ] "{} |- f(2) => 0"

let () =
  ensure_dir "dist";
  ensure_dir "dist/proofs";
  let path = "dist/proofs/core_recursive_f2_stack.svg" in
  V.write_box_svg path tree;
  Printf.printf "Core proof SVG written to %s\n" path;
  let subtree_path = "dist/proofs/core_recursive_f0_subtree.svg" in
  V.write_box_svg subtree_path call0_subtree;
  Printf.printf "Core proof SVG written to %s\n" subtree_path;
  let top_subtree_path = "dist/proofs/core_recursive_f0_subtree_top.svg" in
  V.write_box_svg top_subtree_path call0_subtree_top;
  Printf.printf "Core proof SVG written to %s\n" top_subtree_path
