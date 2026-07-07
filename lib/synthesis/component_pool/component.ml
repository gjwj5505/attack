open Language

(* Component buckets store bottom-up synthesis units: recursive syntax/proof
   structures, plus non-recursive parents that contain recursive component
   children and therefore form reusable intermediate nodes. Thin administrative
   wrappers such as option/list containers are built inside grow rules. *)

module type Payload = sig
  type t
end

module Make_component (Payload : Payload) = struct
  type payload = Payload.t

  type t = {
    payload : payload;
    score : float;
  }

  let make_with_score payload score = { payload; score }
  let make payload = make_with_score payload 0.0
  let payload t = t.payload
  let score t = t.score
end

module Exp_component = Make_component (struct
  type t = Syntax.exp
end)

module Lval_component = Make_component (struct
  type t = Syntax.lval
end)

module Offset_component = Make_component (struct
  type t = Syntax.offset
end)

module Instr_component = Make_component (struct
  type t = Syntax.instr
end)

module Stmt_component = Make_component (struct
  type t = Syntax.stmt
end)

module Block_component = Make_component (struct
  type t = Syntax.block
end)

module Fundec_component = Make_component (struct
  type t = Syntax.fundec
end)

module Init_component = Make_component (struct
  type t = Syntax.init
end)

module Global_component = Make_component (struct
  type t = Syntax.global
end)

module File_component = Make_component (struct
  type t = Syntax.file
end)

module ETree_component = Make_component (struct
  type t = BigStep.etree
end)

module LTree_component = Make_component (struct
  type t = BigStep.ltree
end)

module ITree_component = Make_component (struct
  type t = BigStep.itree
end)

module STree_component = Make_component (struct
  type t = BigStep.stree
end)

module BTree_component = Make_component (struct
  type t = BigStep.btree
end)

module FTree_component = Make_component (struct
  type t = BigStep.ftree
end)

module PTree_component = Make_component (struct
  type t = BigStep.ptree
end)
