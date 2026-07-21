open HoleSyntax

module Box = Pretty.Box

let string_of_varinfo = SyntaxPretty.string_of_varinfo
let string_of_fieldinfo = SyntaxPretty.string_of_fieldinfo
let string_of_constant = SyntaxPretty.string_of_constant
let string_of_unop = SyntaxPretty.string_of_unop
let string_of_binop = SyntaxPretty.string_of_binop
let string_of_label = SyntaxPretty.string_of_label

let string_of_hole id = Printf.sprintf "H%d" id
let named_list name boxes = Box.node name boxes

let rec box_of_exp = function
  | ExpHole id -> Box.leaf "ExpHole" (string_of_hole id)
  | Const constant -> Box.leaf "Const" (string_of_constant constant)
  | Lval lval -> Box.node "Lval" [ box_of_lval lval ]
  | UnOp (op, exp, typ) ->
      Box.node
        (Printf.sprintf "UnOp %s : %s" (string_of_unop op)
           (Typ.string_of_t typ))
        [ box_of_exp exp ]
  | BinOp (op, left, right, typ) ->
      Box.node
        (Printf.sprintf "BinOp %s : %s" (string_of_binop op)
           (Typ.string_of_t typ))
        [ box_of_exp left; box_of_exp right ]
  | AddrOf lval -> Box.node "AddrOf" [ box_of_lval lval ]
  | StartOf lval -> Box.node "StartOf" [ box_of_lval lval ]

and box_of_lval (host, offset) =
  Box.node "lval" [ box_of_lhost host; box_of_offset offset ]

and box_of_lhost = function
  | Var var -> Box.leaf "Var" (string_of_varinfo var)
  | Mem exp -> Box.node "Mem" [ box_of_exp exp ]

and box_of_offset = function
  | NoOffset -> Box.leaf_name "NoOffset"
  | Field (field, offset) ->
      Box.node "Field"
        [ Box.leaf "field" (string_of_fieldinfo field); box_of_offset offset ]
  | Index (exp, offset) ->
      Box.node "Index" [ box_of_exp exp; box_of_offset offset ]

let box_of_option box_of_item name = function
  | None -> Box.node name [ Box.leaf_name "None" ]
  | Some item -> Box.node name [ Box.node "Some" [ box_of_item item ] ]

let box_of_varinfo_list name vars =
  named_list name
    (List.map (fun var -> Box.leaf "varinfo" (string_of_varinfo var)) vars)

let box_of_labels labels =
  named_list "labels"
    (List.map
       (fun label -> Box.leaf "Label" (string_of_label label))
       labels)

let box_of_instr = function
  | Set (lval, exp) -> Box.node "Set" [ box_of_lval lval; box_of_exp exp ]
  | Call (ret, callee, args) ->
      Box.node "Call"
        (box_of_option box_of_lval "ret" ret
        :: box_of_exp callee
        :: List.map box_of_exp args)

let rec box_of_stmt stmt =
  let name =
    match stmt.sid with
    | None -> "stmt"
    | Some sid -> Printf.sprintf "stmt sid=%d" sid
  in
  Box.node name [ box_of_labels stmt.labels; box_of_stmtkind stmt.skind ]

and box_of_stmt_seq_item = function
  | Stmt stmt -> box_of_stmt stmt
  | StmtSeqHole id -> Box.leaf "StmtSeqHole" (string_of_hole id)

and box_of_stmtkind = function
  | Instr instrs -> named_list "Instr" (List.map box_of_instr instrs)
  | Return exp -> Box.node "Return" [ box_of_option box_of_exp "exp" exp ]
  | If (condition, then_block, else_block) ->
      Box.node "If"
        [
          box_of_exp condition;
          Box.node "then" [ box_of_block then_block ];
          Box.node "else" [ box_of_block else_block ];
        ]
  | Loop body -> Box.node "Loop" [ box_of_block body ]
  | Break -> Box.leaf_name "Break"
  | Continue -> Box.leaf_name "Continue"
  | Block block -> Box.node "Block" [ box_of_block block ]

and box_of_block block =
  named_list "block" (List.map box_of_stmt_seq_item block.bstmts)

let rec box_of_init = function
  | SingleInit exp -> Box.node "SingleInit" [ box_of_exp exp ]
  | CompoundInit (typ, fields) ->
      Box.node
        (Printf.sprintf "CompoundInit : %s" (Typ.string_of_t typ))
        (List.map
           (fun (offset, init) ->
             Box.node "field" [ box_of_offset offset; box_of_init init ])
           fields)

let box_of_initinfo initinfo =
  match initinfo.init with
  | None -> Box.node "init" [ Box.leaf_name "None" ]
  | Some init -> Box.node "init" [ Box.node "Some" [ box_of_init init ] ]

let box_of_fundec fundec =
  Box.node "fundec"
    [
      Box.leaf "svar" (string_of_varinfo fundec.svar);
      box_of_varinfo_list "sformals" fundec.sformals;
      box_of_varinfo_list "slocals" fundec.slocals;
      box_of_block fundec.sbody;
    ]

let box_of_global = function
  | GFun fundec -> Box.node "GFun" [ box_of_fundec fundec ]
  | GVarDecl var ->
      Box.node "GVarDecl" [ Box.leaf "varinfo" (string_of_varinfo var) ]
  | GVar (var, initinfo) ->
      Box.node "GVar"
        [ Box.leaf "varinfo" (string_of_varinfo var); box_of_initinfo initinfo ]

let box_of_file file =
  Box.node ("file " ^ file.fileName) (List.map box_of_global file.globals)

let render_file file = Box.render (box_of_file file)
let print_file file = render_file file |> List.iter print_endline
let string_of_file file = Box.to_string (box_of_file file)
let write_file_svg path file = render_file file |> Pretty.Svg.write_lines path
