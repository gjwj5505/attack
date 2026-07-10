module S = Syntax

(* CIL-- calls have a callee expression:

     Call of lval option * Exp.t * Exp.t list

   When function calls are implemented, callee resolution should become an
   explicit proof component, e.g. a callee_tree, so direct calls and later
   function-pointer calls are handled in one place. The call instruction tree
   should describe the caller-side effect of the instruction; the function tree
   should describe callee frame setup, body execution, and return.
*)

type memory = Memory.t
type value = Value.t

type control =
  | Normal
  | ReturnVoid
  | Return of value
  | Break
  | Continue

type loc = Memory.loc

(* expression *)
type e_concl = memory * S.Exp.t * value
(* lval *)
type l_concl = memory * S.lval * loc
(* single instruction : Set, Call *)
type i_concl = memory * S.instr * memory
(* statement : instruction, return, break, continue, if, loop, ... *)
type s_concl = memory * S.stmt * memory * control
(* block *)
type b_concl = memory * S.block * memory * control
(* function *)
type f_concl = memory * S.fundec * value list * memory * control
(* total program : execute main function *)
type p_concl = S.file * memory * value

type tree =
  | ETree of etree
  | LTree of ltree
  | ITree of itree
  | STree of stree
  | BTree of btree
  | FTree of ftree
  | PTree of ptree

and etree =
  | ETreeConst of e_concl
  | ETreeLval of ltree * e_concl
  | ETreeUnOp of etree * e_concl
  | ETreeLogicalOrLeftTrue of etree * e_concl
  | ETreeLogicalOrLeftFalse of etree * etree * e_concl
  | ETreeLogicalAndLeftFalse of etree * e_concl
  | ETreeLogicalAndLeftTrue of etree * etree * e_concl
  | ETreeBinOp of etree * etree * e_concl (* logical 제외 *)
  | ETreeAddrOf of ltree * e_concl
  | ETreeStartOf of ltree * e_concl

and ltree =
  | LTreeVar of l_concl
  | LTreeMem of etree * l_concl
  | LTreeIndex of ltree * etree * l_concl

and itree =
  | ITreeSet of ltree * etree * i_concl
  | ITreeCallVoid of callee_tree * etree list * ftree * i_concl
  | ITreeCallAssign of ltree * callee_tree * etree list * ftree * i_concl

and callee_tree =
  | CalleeTreeDirect of S.Exp.t * S.varinfo * S.fundec

and stree =
  | STreeInstr of itree list * s_concl
  | STreeReturnNone of s_concl
  | STreeReturnSome of etree * s_concl
  | STreeBreak of s_concl
  | STreeContinue of s_concl
  | STreeIfTrue of etree * btree * s_concl
  | STreeIfFalse of etree * btree * s_concl
  | STreeLoopRepeat of btree * stree * s_concl
  | STreeLoopContinue of btree * stree * s_concl
  | STreeLoopBreak of btree * s_concl
  | STreeLoopReturn of btree * s_concl
  | STreeBlock of btree * s_concl

and btree =
  | BTreeSeq of stree list * b_concl

and ftree =
  | FTreeReturn of btree * f_concl
  | FTreeNoReturn of btree * f_concl

and ptree =
  | PTreeMainReturn of ftree * p_concl
