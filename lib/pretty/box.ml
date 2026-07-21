type t = {
  lines : string list;
  width : int;
  height : int;
}

let of_string s =
  let lines = String.split_on_char '\n' s in
  let lines = if lines = [] then [ "" ] else lines in
  let width = List.fold_left (fun acc line -> max acc (String.length line)) 0 lines in
  { lines; width; height = List.length lines }

let empty = { lines = []; width = 0; height = 0 }

let pad_bottom box target_height =
  let difference = target_height - box.height in
  if difference <= 0 then box.lines
  else
    let padding = List.init difference (fun _ -> String.make box.width ' ') in
    padding @ box.lines

let center_lines box width =
  if box.width = 0 && box.height = 0 then []
  else
    let left_padding = (width - box.width) / 2 in
    let right_padding = width - box.width - left_padding in
    List.map
      (fun line ->
        String.make left_padding ' ' ^ line ^ String.make right_padding ' ')
      box.lines

let horizontal boxes =
  let gap = 3 in
  match boxes with
  | [] -> empty
  | [ box ] -> box
  | boxes ->
      let max_height =
        List.fold_left (fun acc box -> max acc box.height) 0 boxes
      in
      let padded =
        List.map
          (fun box ->
            {
              box with
              lines = pad_bottom box max_height;
              height = max_height;
            })
          boxes
      in
      List.fold_left
        (fun acc box ->
          let lines =
            List.map2
              (fun left right -> left ^ String.make gap ' ' ^ right)
              acc.lines box.lines
          in
          {
            lines;
            width = acc.width + gap + box.width;
            height = max_height;
          })
        (List.hd padded) (List.tl padded)

let node name children =
  let children = horizontal children in
  let label = of_string ("[" ^ name ^ "]") in
  let width = max children.width label.width in
  let separator = String.make width '-' in
  let child_lines = center_lines children width in
  let label_lines = center_lines label width in
  {
    lines = child_lines @ [ separator ] @ label_lines;
    width;
    height = List.length child_lines + 1 + List.length label_lines;
  }

let leaf name value = node (name ^ " " ^ value) []
let leaf_name name = node name []
let render box = box.lines
let to_string box = String.concat "\n" (render box)
