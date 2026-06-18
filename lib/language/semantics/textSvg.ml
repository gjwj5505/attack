let escape_xml ?(preserve_space = false) s =
  let b = Buffer.create (String.length s) in
  String.iter
    (function
      | '&' -> Buffer.add_string b "&amp;"
      | '<' -> Buffer.add_string b "&lt;"
      | '>' -> Buffer.add_string b "&gt;"
      | '"' -> Buffer.add_string b "&quot;"
      | '\'' -> Buffer.add_string b "&apos;"
      | ' ' when preserve_space -> Buffer.add_string b "&#160;"
      | c -> Buffer.add_char b c)
    s;
  Buffer.contents b

let write_lines path lines =
  let char_width = 8 in
  let line_height = 16 in
  let margin = 16 in
  let max_len =
    List.fold_left (fun acc line -> max acc (String.length line)) 0 lines
  in
  let width = max 1 ((max_len * char_width) + (2 * margin)) in
  let height = max 1 ((List.length lines * line_height) + (2 * margin)) in
  let oc = open_out path in
  Fun.protect
    ~finally:(fun () -> close_out_noerr oc)
    (fun () ->
      Printf.fprintf oc
        "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n\
         <svg xmlns=\"http://www.w3.org/2000/svg\" width=\"%d\" height=\"%d\" \
         viewBox=\"0 0 %d %d\">\n\
         <rect width=\"100%%\" height=\"100%%\" fill=\"white\"/>\n\
         <g font-family=\"DejaVu Sans Mono, Liberation Mono, Consolas, monospace\" \
         font-size=\"13\" fill=\"black\" xml:space=\"preserve\" \
         style=\"white-space: pre; font-variant-ligatures: none;\">\n"
        width height width height;
      List.iter
        (fun (i, line) ->
          let y = margin + ((i + 1) * line_height) in
          Printf.fprintf oc "<text x=\"%d\" y=\"%d\">%s</text>\n" margin y
            (escape_xml ~preserve_space:true line))
        (List.mapi (fun i line -> (i, line)) lines);
      Printf.fprintf oc "</g>\n</svg>\n")
