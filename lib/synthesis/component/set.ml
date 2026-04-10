open Language.Syntax
open Language.Syntax.BigStep

module Size = Component_size

module ExpOrd = struct
  type t = Exp.t
  let compare = Stdlib.compare
end

module CmdOrd = struct
  type t = Cmd.t
  let compare = Stdlib.compare
end

module ETreeOrd = struct
  type t = etree
  let compare = Stdlib.compare
end

module CTreeOrd = struct
  type t = ctree
  let compare = Stdlib.compare
end

module ExpSet = Set.Make(ExpOrd)
module CmdSet = Set.Make(CmdOrd)
module ETreeSet = Set.Make(ETreeOrd)
module CTreeSet = Set.Make(CTreeOrd)

type component_bucket =
  { exps   : ExpSet.t
  ; cmds   : CmdSet.t
  ; etrees : ETreeSet.t
  ; ctrees : CTreeSet.t
  }

type component_table = component_bucket array

