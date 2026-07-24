open BigStep

type size = { prog_size : int; proof_size : int }

let make prog_size proof_size = { prog_size; proof_size }
let prog_size s = s.prog_size
let proof_size s = s.proof_size
let total s = s.prog_size + s.proof_size

let compare a b =
  match Int.compare (total a) (total b) with
  | 0 -> Int.compare b.prog_size a.prog_size
  | n -> n

let equal a b = compare a b = 0

let add a b =
  {
    prog_size = a.prog_size + b.prog_size;
    proof_size = a.proof_size + b.proof_size;
  }

let sub a b =
  {
    prog_size = a.prog_size - b.prog_size;
    proof_size = a.proof_size - b.proof_size;
  }

let is_valid { prog_size; proof_size } = prog_size >= 0 && proof_size >= 0

let is_prog_component { prog_size; proof_size } =
  prog_size >= 1 && proof_size = 0

let is_proof_component { prog_size; proof_size } =
  prog_size >= 1 && proof_size >= 1

let to_string s = Printf.sprintf "(%d,%d)" s.prog_size s.proof_size

module Map = Map.Make (struct
  type nonrec t = size

  let compare = compare
end)

let sizeof_varinfo _ = 1
let sizeof_fieldinfo _ = 1
let sizeof_constant _ = 1

let rec sizeof_exp = function
  | Syntax.Const c -> 1 + sizeof_constant c
  | Syntax.Lval lval -> 1 + sizeof_lval lval
  | Syntax.UnOp (_, exp, _typ) -> 1 + sizeof_exp exp
  | Syntax.BinOp (_, left, right, _typ) ->
      1 + sizeof_exp left + sizeof_exp right
  | Syntax.AddrOf lval | Syntax.StartOf lval -> 1 + sizeof_lval lval

and sizeof_lval (host, offset) = sizeof_lhost host + sizeof_offset offset

and sizeof_lhost = function
  | Syntax.Var var -> 1 + sizeof_varinfo var
  | Syntax.Mem exp -> 1 + sizeof_exp exp

and sizeof_offset = function
  | Syntax.NoOffset -> 1
  | Syntax.Field (field, offset) ->
      1 + sizeof_fieldinfo field + sizeof_offset offset
  | Syntax.Index (exp, offset) -> 1 + sizeof_exp exp + sizeof_offset offset

let sizeof_instr = function
  | Syntax.Set (lval, exp) -> 1 + sizeof_lval lval + sizeof_exp exp
  | Syntax.Call (ret, callee, args) ->
      1
      + Option.fold ~none:0 ~some:sizeof_lval ret
      + sizeof_exp callee
      + List.fold_left (fun acc arg -> acc + sizeof_exp arg) 0 args

let rec sizeof_stmt stmt =
  match stmt.Syntax.skind with
  | Syntax.Instr instrs ->
      1 + List.fold_left (fun acc instr -> acc + sizeof_instr instr) 0 instrs
  | Syntax.Return None -> 1
  | Syntax.Return (Some exp) -> 1 + sizeof_exp exp
  | Syntax.If (cond, then_block, else_block) ->
      1 + sizeof_exp cond + sizeof_block then_block + sizeof_block else_block
  | Syntax.Loop body -> 1 + sizeof_block body
  | Syntax.Break | Syntax.Continue -> 1
  | Syntax.Block block -> 1 + sizeof_block block

and sizeof_block block =
  1 + List.fold_left (fun acc stmt -> acc + sizeof_stmt stmt) 0 block.Syntax.bstmts

let sizeof_fundec fd =
  1 + sizeof_varinfo fd.Syntax.svar
  + List.fold_left (fun acc formal -> acc + sizeof_varinfo formal) 0 fd.Syntax.sformals
  + List.fold_left (fun acc local -> acc + sizeof_varinfo local) 0 fd.Syntax.slocals
  + sizeof_block fd.Syntax.sbody

let rec sizeof_initinfo initinfo =
  match initinfo.Syntax.init with
  | None -> 0
  | Some init -> sizeof_init init

and sizeof_init = function
  | Syntax.SingleInit exp -> 1 + sizeof_exp exp
  | Syntax.CompoundInit (_typ, fields) ->
      1
      + List.fold_left
          (fun acc (offset, init) -> acc + sizeof_offset offset + sizeof_init init)
          0 fields

let sizeof_global = function
  | Syntax.GFun fd -> sizeof_fundec fd
  | Syntax.GVarDecl var -> 1 + sizeof_varinfo var
  | Syntax.GVar (var, initinfo) ->
      1 + sizeof_varinfo var + sizeof_initinfo initinfo

let sizeof_file file =
  1 + List.fold_left (fun acc global -> acc + sizeof_global global) 0 file.Syntax.globals

let sizeof_callee_tree = function
  | CalleeTreeDirect _ -> 1

let rec sizeof_etree = function
  | ETreeConst _ -> 1
  | ETreeLval (ltree, _) -> 1 + sizeof_ltree ltree
  | ETreeUnOp (etree, _) -> 1 + sizeof_etree etree
  | ETreeLogicalOrLeftTrue (left, _) -> 1 + sizeof_etree left
  | ETreeLogicalOrLeftFalse (left, right, _)
  | ETreeLogicalAndLeftTrue (left, right, _)
  | ETreeBinOp (left, right, _) ->
      1 + sizeof_etree left + sizeof_etree right
  | ETreeLogicalAndLeftFalse (left, _) -> 1 + sizeof_etree left
  | ETreeAddrOf (ltree, _) | ETreeStartOf (ltree, _) -> 1 + sizeof_ltree ltree

and sizeof_ltree = function
  | LTreeVar _ -> 1
  | LTreeMem (etree, _) -> 1 + sizeof_etree etree
  | LTreeIndex (ltree, etree, _) -> 1 + sizeof_ltree ltree + sizeof_etree etree

and sizeof_itree = function
  | ITreeSet (ltree, etree, _) -> 1 + sizeof_ltree ltree + sizeof_etree etree
  | ITreeCallVoid (callee, args, ftree, _) ->
      1 + sizeof_callee_tree callee
      + List.fold_left (fun acc arg -> acc + sizeof_etree arg) 0 args
      + sizeof_ftree ftree
  | ITreeCallAssign (ltree, callee, args, ftree, _) ->
      1 + sizeof_ltree ltree + sizeof_callee_tree callee
      + List.fold_left (fun acc arg -> acc + sizeof_etree arg) 0 args
      + sizeof_ftree ftree

and sizeof_stree = function
  | STreeInstr (itrees, _) ->
      1 + List.fold_left (fun acc itree -> acc + sizeof_itree itree) 0 itrees
  | STreeReturnNone _ | STreeBreak _ | STreeContinue _ -> 1
  | STreeReturnSome (etree, _) -> 1 + sizeof_etree etree
  | STreeIfTrue (cond, body, _) | STreeIfFalse (cond, body, _) ->
      1 + sizeof_etree cond + sizeof_btree body
  | STreeLoopRepeat (body, rest, _) | STreeLoopContinue (body, rest, _) ->
      1 + sizeof_btree body + sizeof_stree rest
  | STreeLoopBreak (body, _) | STreeLoopReturn (body, _) | STreeBlock (body, _) ->
      1 + sizeof_btree body

and sizeof_btree = function
  | BTreeSeq (strees, _) ->
      1 + List.fold_left (fun acc stree -> acc + sizeof_stree stree) 0 strees

and sizeof_ftree = function
  | FTreeReturn (btree, _) | FTreeNoReturn (btree, _) -> 1 + sizeof_btree btree

let sizeof_ptree = function
  | PTreeMainReturn (ftree, _) -> 1 + sizeof_ftree ftree

let sizeof_proof = function
  | ETree etree -> sizeof_etree etree
  | LTree ltree -> sizeof_ltree ltree
  | ITree itree -> sizeof_itree itree
  | STree stree -> sizeof_stree stree
  | BTree btree -> sizeof_btree btree
  | FTree ftree -> sizeof_ftree ftree
  | PTree ptree -> sizeof_ptree ptree

let sizeof_conclusion_prog = function
  | ETree etree ->
      let _, exp, _ = BigStepUtil.e_concl etree in
      sizeof_exp exp
  | LTree ltree ->
      let _, lval, _ = BigStepUtil.l_concl ltree in
      sizeof_lval lval
  | ITree itree ->
      let _, instr, _ = BigStepUtil.i_concl itree in
      sizeof_instr instr
  | STree stree ->
      let _, stmt, _, _ = BigStepUtil.s_concl stree in
      sizeof_stmt stmt
  | BTree btree ->
      let _, block, _, _ = BigStepUtil.b_concl btree in
      sizeof_block block
  | FTree ftree ->
      let _, fd, _, _, _ = BigStepUtil.f_concl ftree in
      sizeof_fundec fd
  | PTree ptree ->
      let file, _, _ = BigStepUtil.p_concl ptree in
      sizeof_file file

let sizeof_tree tree =
  { prog_size = sizeof_conclusion_prog tree; proof_size = sizeof_proof tree }
