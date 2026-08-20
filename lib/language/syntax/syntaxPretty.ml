open Syntax

module Box = Pretty.Box

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

let named_list name boxes = Box.node name boxes

let rec box_of_exp : type mode. mode exp -> Box.t = function
  | ExpHole id -> Box.leaf "ExpHole" (Printf.sprintf "H%d" id)
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

and box_of_lval : type mode. mode lval -> Box.t =
 fun (host, offset) ->
  Box.node "lval" [ box_of_lhost host; box_of_offset offset ]

and box_of_lhost : type mode. mode lhost -> Box.t = function
  | Var var -> Box.leaf "Var" (string_of_varinfo var)
  | Mem exp -> Box.node "Mem" [ box_of_exp exp ]

and box_of_offset : type mode. mode offset -> Box.t = function
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

let rec box_of_stmt : type mode. mode stmt -> Box.t = fun stmt ->
  let name =
    match stmt.sid with
    | None -> "stmt"
    | Some sid -> Printf.sprintf "stmt sid=%d" sid
  in
  Box.node name [ box_of_labels stmt.labels; box_of_stmtkind stmt.skind ]

and box_of_stmtkind : type mode. mode stmtkind -> Box.t = function
  | Instr instrs -> named_list "Instr" (List.map box_of_instr instrs)
  | Return exp -> Box.node "Return" [ box_of_option box_of_exp "exp" exp ]
  | If (cond, then_block, else_block) ->
      Box.node "If"
        [
          box_of_exp cond;
          Box.node "then" [ box_of_block then_block ];
          Box.node "else" [ box_of_block else_block ];
        ]
  | Loop body -> Box.node "Loop" [ box_of_block body ]
  | Break -> Box.leaf_name "Break"
  | Continue -> Box.leaf_name "Continue"
  | Block block -> Box.node "Block" [ box_of_block block ]

and box_of_stmt_seq_item : type mode. mode stmt_seq_item -> Box.t = function
  | Stmt stmt -> box_of_stmt stmt
  | StmtSeqHole id -> Box.leaf "StmtSeqHole" (Printf.sprintf "H%d" id)

and box_of_block : type mode. mode block -> Box.t = fun block ->
  named_list "block" (List.map box_of_stmt_seq_item block.bstmts)

let rec box_of_init : type mode. mode init -> Box.t = function
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
  Box.node
    (Printf.sprintf "file %s size %s" file.fileName
       (Size.to_string (SyntaxSize.sizeof_file file)))
    (List.map box_of_global file.globals)

let render_file file = Box.render (box_of_file file)
let print_file file = render_file file |> List.iter print_endline
let string_of_file file = Box.to_string (box_of_file file)
let write_file_svg path file = render_file file |> Pretty.Svg.write_lines path
