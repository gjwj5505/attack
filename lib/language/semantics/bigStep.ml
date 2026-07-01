module S = Syntax

(* CIL' calls have a callee expression:

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
  | EConst of e_concl
  | ELval of ltree * e_concl
  | EUnOp of etree * e_concl
  | ELogicalOrLeftTrue of etree * e_concl
  | ELogicalOrLeftFalse of etree * etree * e_concl
  | ELogicalAndLeftFalse of etree * e_concl
  | ELogicalAndLeftTrue of etree * etree * e_concl
  | EBinOp of etree * etree * e_concl (* logical 제외 *)
  | EAddrOf of ltree * e_concl
  | EStartOf of ltree * e_concl

and ltree =
  | LVar of l_concl
  | LMem of etree * l_concl
  | LIndex of ltree * etree * l_concl

and itree =
  | ISet of ltree * etree * i_concl
  | ICallVoid of callee_tree * etree list * ftree * i_concl
  | ICallAssign of ltree * callee_tree * etree list * ftree * i_concl

and callee_tree =
  | DirectCallee of S.Exp.t * S.varinfo * S.fundec

and stree =
  | SInstr of itree list * s_concl
  | SReturnNone of s_concl
  | SReturnSome of etree * s_concl
  | SBreak of s_concl
  | SContinue of s_concl
  | SIfTrue of etree * btree * s_concl
  | SIfFalse of etree * btree * s_concl
  | SLoopRepeat of btree * stree * s_concl
  | SLoopContinue of btree * stree * s_concl
  | SLoopBreak of btree * s_concl
  | SLoopReturn of btree * s_concl
  | SBlock of btree * s_concl

and btree =
  | BEmpty of b_concl
  | BSeqNormal of stree * btree * b_concl
  | BSeqReturn of stree * b_concl
  | BSeqBreak of stree * b_concl
  | BSeqContinue of stree * b_concl

and ftree =
  | FReturn of btree * f_concl
  | FNoReturn of btree * f_concl

and ptree =
  | PMainReturn of ftree * p_concl
