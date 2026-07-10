open Syntax

type box = {
  lines : string list;
  width : int;
  height : int;
}

type side =
  | Top
  | Bottom

let make_box s =
  let lines = String.split_on_char '\n' s in
  let lines = if lines = [] then [ "" ] else lines in
  let width = List.fold_left (fun acc l -> max acc (String.length l)) 0 lines in
  { lines; width; height = List.length lines }

let empty_box = { lines = []; width = 0; height = 0 }

let pad side b target_h =
  let diff = target_h - b.height in
  if diff <= 0 then b.lines
  else
    let padding = List.init diff (fun _ -> String.make b.width ' ') in
    match side with
    | Top -> b.lines @ padding
    | Bottom -> padding @ b.lines

let center_lines b w =
  if b.width = 0 && b.height = 0 then []
  else
    let left_pad = (w - b.width) / 2 in
    let right_pad = w - b.width - left_pad in
    List.map
      (fun s -> String.make left_pad ' ' ^ s ^ String.make right_pad ' ')
      b.lines

let hbox boxes =
  let gap = 3 in
  match boxes with
  | [] -> empty_box
  | [ b ] -> b
  | boxes ->
      let max_h = List.fold_left (fun acc b -> max acc b.height) 0 boxes in
      let padded =
        List.map
          (fun b -> { b with lines = pad Bottom b max_h; height = max_h })
          boxes
      in
      List.fold_left
        (fun acc b ->
          let lines =
            List.map2
              (fun left right -> left ^ String.make gap ' ' ^ right)
              acc.lines b.lines
          in
          {
            lines;
            width = acc.width + gap + b.width;
            height = max_h;
          })
        (List.hd padded) (List.tl padded)

let build_node name children =
  let child_box = hbox children in
  let label = make_box ("[" ^ name ^ "]") in
  let width = max child_box.width label.width in
  let line = String.make width '-' in
  let child_lines = center_lines child_box width in
  let label_lines = center_lines label width in
  {
    lines = child_lines @ [ line ] @ label_lines;
    width;
    height = List.length child_lines + 1 + List.length label_lines;
  }

let leaf name value = build_node (name ^ " " ^ value) []
let leaf_name name = build_node name []

let string_of_varinfo v =
  Printf.sprintf "%s : %s%s" (SyntaxUtil.string_of_var v)
    (Typ.string_of_t v.vtype)
    (if v.vglob then " global" else "")

let string_of_fieldinfo f =
  Printf.sprintf "%s : %s" f.fname (Typ.string_of_t f.ftype)

let string_of_constant = function
  | CInt (n, Typ.IInt) -> Int64.to_string n
  | CInt (n, Typ.IUInt) -> Int64.to_string n ^ "U"

let string_of_unop = function
  | Neg -> "Neg"
  | BNot -> "BNot"
  | LNot -> "LNot"

let string_of_binop = function
  | PlusA -> "PlusA"
  | PlusPI -> "PlusPI"
  | IndexPI -> "IndexPI"
  | MinusA -> "MinusA"
  | MinusPI -> "MinusPI"
  | MinusPP -> "MinusPP"
  | Mult -> "Mult"
  | Div -> "Div"
  | Mod -> "Mod"
  | Shiftlt -> "Shiftlt"
  | Shiftrt -> "Shiftrt"
  | Lt -> "Lt"
  | Gt -> "Gt"
  | Le -> "Le"
  | Ge -> "Ge"
  | Eq -> "Eq"
  | Ne -> "Ne"
  | BAnd -> "BAnd"
  | BXor -> "BXor"
  | BOr -> "BOr"
  | LAnd -> "LAnd"
  | LOr -> "LOr"

let string_of_label = function
  | Label name -> name

let named_list name boxes = build_node name boxes

let rec box_of_exp = function
  | Const c -> leaf "Const" (string_of_constant c)
  | Lval lval -> build_node "Lval" [ box_of_lval lval ]
  | UnOp (op, exp, typ) ->
      build_node
        (Printf.sprintf "UnOp %s : %s" (string_of_unop op)
           (Typ.string_of_t typ))
        [ box_of_exp exp ]
  | BinOp (op, left, right, typ) ->
      build_node
        (Printf.sprintf "BinOp %s : %s" (string_of_binop op)
           (Typ.string_of_t typ))
        [ box_of_exp left; box_of_exp right ]
  | AddrOf lval -> build_node "AddrOf" [ box_of_lval lval ]
  | StartOf lval -> build_node "StartOf" [ box_of_lval lval ]

and box_of_lval (host, offset) =
  build_node "lval" [ box_of_lhost host; box_of_offset offset ]

and box_of_lhost = function
  | Var v -> leaf "Var" (string_of_varinfo v)
  | Mem exp -> build_node "Mem" [ box_of_exp exp ]

and box_of_offset = function
  | NoOffset -> leaf_name "NoOffset"
  | Field (field, offset) ->
      build_node "Field" [ leaf "field" (string_of_fieldinfo field); box_of_offset offset ]
  | Index (exp, offset) -> build_node "Index" [ box_of_exp exp; box_of_offset offset ]

let box_of_option box_of_item name = function
  | None -> build_node name [ leaf_name "None" ]
  | Some item -> build_node name [ build_node "Some" [ box_of_item item ] ]

let box_of_varinfo_list name vars =
  named_list name (List.map (fun v -> leaf "varinfo" (string_of_varinfo v)) vars)

let box_of_labels labels =
  named_list "labels" (List.map (fun label -> leaf "Label" (string_of_label label)) labels)

let box_of_instr = function
  | Set (lval, exp) -> build_node "Set" [ box_of_lval lval; box_of_exp exp ]
  | Call (ret, callee, args) ->
      build_node "Call"
        (box_of_option box_of_lval "ret" ret
        :: box_of_exp callee
        :: List.map box_of_exp args)

let rec box_of_stmt stmt =
  let name =
    match stmt.sid with
    | None -> "stmt"
    | Some sid -> Printf.sprintf "stmt sid=%d" sid
  in
  build_node name [ box_of_labels stmt.labels; box_of_stmtkind stmt.skind ]

and box_of_stmtkind = function
  | Instr instrs -> named_list "Instr" (List.map box_of_instr instrs)
  | Return exp -> build_node "Return" [ box_of_option box_of_exp "exp" exp ]
  | If (cond, then_block, else_block) ->
      build_node "If"
        [ box_of_exp cond;
          build_node "then" [ box_of_block then_block ];
          build_node "else" [ box_of_block else_block ] ]
  | Loop body -> build_node "Loop" [ box_of_block body ]
  | Break -> leaf_name "Break"
  | Continue -> leaf_name "Continue"
  | Block block -> build_node "Block" [ box_of_block block ]

and box_of_block block =
  named_list "block" (List.map box_of_stmt block.bstmts)

let rec box_of_init = function
  | SingleInit exp -> build_node "SingleInit" [ box_of_exp exp ]
  | CompoundInit (typ, fields) ->
      build_node
        (Printf.sprintf "CompoundInit : %s" (Typ.string_of_t typ))
        (List.map
           (fun (offset, init) ->
             build_node "field" [ box_of_offset offset; box_of_init init ])
           fields)

let box_of_initinfo initinfo =
  match initinfo.init with
  | None -> build_node "init" [ leaf_name "None" ]
  | Some init -> build_node "init" [ build_node "Some" [ box_of_init init ] ]

let box_of_fundec fd =
  build_node "fundec"
    [ leaf "svar" (string_of_varinfo fd.svar);
      box_of_varinfo_list "sformals" fd.sformals;
      box_of_varinfo_list "slocals" fd.slocals;
      box_of_block fd.sbody ]

let box_of_global = function
  | GFun fd -> build_node "GFun" [ box_of_fundec fd ]
  | GVarDecl var -> build_node "GVarDecl" [ leaf "varinfo" (string_of_varinfo var) ]
  | GVar (var, initinfo) ->
      build_node "GVar" [ leaf "varinfo" (string_of_varinfo var); box_of_initinfo initinfo ]

let box_of_file file =
  build_node
    (Printf.sprintf "file %s size %s" file.fileName
       (Size.to_string (Size.make (Size.sizeof_file file) 0)))
    (List.map box_of_global file.globals)

let render_file file = (box_of_file file).lines
let print_file file = render_file file |> List.iter print_endline
let string_of_file file = render_file file |> String.concat "\n"
let write_file_svg path file = render_file file |> TextSvg.write_lines path
