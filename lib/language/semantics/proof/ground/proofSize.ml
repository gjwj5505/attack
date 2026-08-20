open BigStep

let sizeof_callee_tree = function
  | CalleeTreeDirect _ -> 1

let rec sizeof_etree = function
  | ETreeConst _ -> 1
  | ETreeLval (ltree, _) -> 1 + sizeof_ltree ltree
  | ETreeUnOp (etree, _) -> 1 + sizeof_etree etree
  | ETreeLogicalOrLeftTrue (left, _)
  | ETreeLogicalAndLeftFalse (left, _) ->
      1 + sizeof_etree left
  | ETreeLogicalOrLeftFalse (left, right, _)
  | ETreeLogicalAndLeftTrue (left, right, _)
  | ETreeBinOp (left, right, _) ->
      1 + sizeof_etree left + sizeof_etree right
  | ETreeAddrOf (ltree, _) | ETreeStartOf (ltree, _) ->
      1 + sizeof_ltree ltree

and sizeof_ltree = function
  | LTreeVar _ -> 1
  | LTreeMem (etree, _) -> 1 + sizeof_etree etree
  | LTreeIndex (ltree, etree, _) ->
      1 + sizeof_ltree ltree + sizeof_etree etree

and sizeof_itree = function
  | ITreeSet (ltree, etree, _) ->
      1 + sizeof_ltree ltree + sizeof_etree etree
  | ITreeCallVoid (callee, arguments, ftree, _) ->
      1 + sizeof_callee_tree callee
      + List.fold_left
          (fun size argument -> size + sizeof_etree argument)
          0 arguments
      + sizeof_ftree ftree
  | ITreeCallAssign (ltree, callee, arguments, ftree, _) ->
      1 + sizeof_ltree ltree + sizeof_callee_tree callee
      + List.fold_left
          (fun size argument -> size + sizeof_etree argument)
          0 arguments
      + sizeof_ftree ftree

and sizeof_stree = function
  | STreeInstr (itrees, _) ->
      1
      + List.fold_left
          (fun size itree -> size + sizeof_itree itree)
          0 itrees
  | STreeReturnNone _ | STreeBreak _ | STreeContinue _ -> 1
  | STreeReturnSome (etree, _) -> 1 + sizeof_etree etree
  | STreeIfTrue (condition, body, _)
  | STreeIfFalse (condition, body, _) ->
      1 + sizeof_etree condition + sizeof_btree body
  | STreeLoopRepeat (body, rest, _)
  | STreeLoopContinue (body, rest, _) ->
      1 + sizeof_btree body + sizeof_stree rest
  | STreeLoopBreak (body, _) | STreeLoopReturn (body, _)
  | STreeBlock (body, _) ->
      1 + sizeof_btree body

and sizeof_btree = function
  | BTreeSeq (strees, _) ->
      1
      + List.fold_left
          (fun size stree -> size + sizeof_stree stree)
          0 strees

and sizeof_ftree = function
  | FTreeReturn (btree, _) | FTreeNoReturn (btree, _) ->
      1 + sizeof_btree btree

let sizeof_ptree = function
  | PTreeMainReturn (ftree, _) -> 1 + sizeof_ftree ftree

let sizeof_tree = function
  | ETree etree -> sizeof_etree etree
  | LTree ltree -> sizeof_ltree ltree
  | ITree itree -> sizeof_itree itree
  | STree stree -> sizeof_stree stree
  | BTree btree -> sizeof_btree btree
  | FTree ftree -> sizeof_ftree ftree
  | PTree ptree -> sizeof_ptree ptree
