type memory = Memory.t
type value = Value.t

type control =
  | Normal
  | ReturnVoid
  | Return of value
  | Break
  | Continue

type loc = Memory.loc

type 'mode e_concl = memory * 'mode Syntax.exp * value
type 'mode l_concl = memory * 'mode Syntax.lval * loc
type 'mode i_concl = memory * 'mode Syntax.instr * memory
type 'mode s_concl = memory * 'mode Syntax.stmt * memory * control
type 'mode b_concl = memory * 'mode Syntax.block * memory * control

type 'mode f_concl =
  memory * 'mode Syntax.fundec * value list * memory * control

type 'mode p_concl = 'mode Syntax.file * memory * value

type 'mode tree =
  | ETree of 'mode etree
  | LTree of 'mode ltree
  | ITree of 'mode itree
  | STree of 'mode stree
  | BTree of 'mode btree
  | FTree of 'mode ftree
  | PTree of 'mode ptree

and 'mode etree =
  | ETreeConst of 'mode e_concl
  | ETreeLval of 'mode ltree * 'mode e_concl
  | ETreeUnOp of 'mode etree * 'mode e_concl
  | ETreeLogicalOrLeftTrue of 'mode etree * 'mode e_concl
  | ETreeLogicalOrLeftFalse of
      'mode etree * 'mode etree * 'mode e_concl
  | ETreeLogicalAndLeftFalse of 'mode etree * 'mode e_concl
  | ETreeLogicalAndLeftTrue of
      'mode etree * 'mode etree * 'mode e_concl
  | ETreeBinOp of 'mode etree * 'mode etree * 'mode e_concl
  | ETreeAddrOf of 'mode ltree * 'mode e_concl
  | ETreeStartOf of 'mode ltree * 'mode e_concl

and 'mode ltree =
  | LTreeVar of 'mode l_concl
  | LTreeMem of 'mode etree * 'mode l_concl
  | LTreeIndex of 'mode ltree * 'mode etree * 'mode l_concl

and 'mode itree =
  | ITreeSet of 'mode ltree * 'mode etree * 'mode i_concl
  | ITreeCallVoid of
      'mode callee_tree * 'mode etree list * 'mode ftree * 'mode i_concl
  | ITreeCallAssign of
      'mode ltree
      * 'mode callee_tree
      * 'mode etree list
      * 'mode ftree
      * 'mode i_concl

and 'mode callee_tree =
  | CalleeTreeDirect of
      'mode Syntax.exp * Syntax.varinfo * 'mode Syntax.fundec

and 'mode stree =
  | STreeInstr of 'mode itree list * 'mode s_concl
  | STreeReturnNone of 'mode s_concl
  | STreeReturnSome of 'mode etree * 'mode s_concl
  | STreeBreak of 'mode s_concl
  | STreeContinue of 'mode s_concl
  | STreeIfTrue of 'mode etree * 'mode btree * 'mode s_concl
  | STreeIfFalse of 'mode etree * 'mode btree * 'mode s_concl
  | STreeLoopRepeat of 'mode btree * 'mode stree * 'mode s_concl
  | STreeLoopContinue of 'mode btree * 'mode stree * 'mode s_concl
  | STreeLoopBreak of 'mode btree * 'mode s_concl
  | STreeLoopReturn of 'mode btree * 'mode s_concl
  | STreeBlock of 'mode btree * 'mode s_concl

and 'mode btree =
  | BTreeSeq of 'mode stree list * 'mode b_concl

and 'mode ftree =
  | FTreeReturn of 'mode btree * 'mode f_concl
  | FTreeNoReturn of 'mode btree * 'mode f_concl

and 'mode ptree =
  | PTreeMainReturn of 'mode ftree * 'mode p_concl

type ground_tree = Syntax.ground tree
type holed_tree = Syntax.holed tree
