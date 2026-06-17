open Syntax

type memory = Memory.t
type value = Value.t

type control =
  | Normal
  | Return of value
  | Break
  | Continue

type e_concl = memory * Exp.t * memory * value
type s_concl = memory * Stmt.t * memory * control
type b_concl = memory * Stmt.codeblock * memory * control
type p_concl = program * memory * value

type tree =
  | ETree of etree
  | STree of stree
  | BTree of btree
  | PTree of ptree

and etree =
  | EIntLiteral of unit * e_concl
  | ENegIntLiteral of unit * e_concl
  | ELval of unit * e_concl
  | EBop of (etree * etree) * e_concl
  | EUop of etree * e_concl
  (* Future short-circuit logical operators need separate rules. Reusing EBop
     would force a fake right-hand subtree even when C would not evaluate it.
     The constructor names describe the left operand's truthiness, not the whole
     expression result. Checker code must verify that left-result condition. *)
  | ELogicalOrLeftTrue of etree * e_concl
  | ELogicalOrLeftFalse of (etree * etree) * e_concl
  | ELogicalAndLeftFalse of etree * e_concl
  | ELogicalAndLeftTrue of (etree * etree) * e_concl

and stree =
  | SDecl of etree * s_concl
  | SAssign of etree * s_concl
  | SIfTrue of (etree * btree) * s_concl
  | SIfFalse of (etree * btree) * s_concl
  | SWhileFalse of etree * s_concl
  | SWhileTrueNormal of (etree * btree * stree) * s_concl
  | SWhileTrueContinue of (etree * btree * stree) * s_concl
  | SWhileTrueBreak of (etree * btree) * s_concl
  | SWhileTrueReturn of (etree * btree) * s_concl
  | SReturn of etree * s_concl

and btree =
  | BEmpty of b_concl
  | BSeqNormal of (stree * btree) * b_concl
  | BSeqReturn of stree * b_concl
  | BSeqBreak of stree * b_concl
  | BSeqContinue of stree * b_concl

and ptree =
  | PMainReturn of btree * p_concl
