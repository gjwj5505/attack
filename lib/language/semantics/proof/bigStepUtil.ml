open BigStep

let is_normal = function
  | Normal -> true
  | ReturnVoid | Return _ | Break | Continue -> false

let is_return = function
  | ReturnVoid | Return _ -> true
  | Normal | Break | Continue -> false

let is_break = function
  | Break -> true
  | Normal | ReturnVoid | Return _ | Continue -> false

let is_continue = function
  | Continue -> true
  | Normal | ReturnVoid | Return _ | Break -> false

let return_value = function
  | Return value -> Some value
  | Normal | ReturnVoid | Break | Continue -> None

let string_of_control = function
  | Normal -> "Normal"
  | ReturnVoid -> "ReturnVoid"
  | Return value -> "Return(" ^ Value.string_of_t value ^ ")"
  | Break -> "Break"
  | Continue -> "Continue"

let e_concl = function
  | ETreeConst concl
  | ETreeLval (_, concl)
  | ETreeUnOp (_, concl)
  | ETreeLogicalOrLeftTrue (_, concl)
  | ETreeLogicalOrLeftFalse (_, _, concl)
  | ETreeLogicalAndLeftFalse (_, concl)
  | ETreeLogicalAndLeftTrue (_, _, concl)
  | ETreeBinOp (_, _, concl)
  | ETreeAddrOf (_, concl)
  | ETreeStartOf (_, concl) ->
      concl

let e_value tree =
  let _, _, value = e_concl tree in
  value

let l_concl = function
  | LTreeVar concl | LTreeMem (_, concl) | LTreeIndex (_, _, concl) -> concl

let l_loc tree =
  let _, _, loc = l_concl tree in
  loc

let i_concl = function
  | ITreeSet (_, _, concl)
  | ITreeCallVoid (_, _, _, concl)
  | ITreeCallAssign (_, _, _, _, concl) ->
      concl

let i_output_memory tree =
  let _, _, mem = i_concl tree in
  mem

let instrs_output_memory initial_mem = function
  | [] -> initial_mem
  | itrees -> i_output_memory (List.hd (List.rev itrees))

let callee_fundec = function
  | CalleeTreeDirect (_, _, fd) -> fd

let s_concl = function
  | STreeInstr (_, concl)
  | STreeReturnNone concl
  | STreeReturnSome (_, concl)
  | STreeBreak concl
  | STreeContinue concl
  | STreeIfTrue (_, _, concl)
  | STreeIfFalse (_, _, concl)
  | STreeLoopRepeat (_, _, concl)
  | STreeLoopContinue (_, _, concl)
  | STreeLoopBreak (_, concl)
  | STreeLoopReturn (_, concl)
  | STreeBlock (_, concl) ->
      concl

let s_output_memory tree =
  let _, _, mem, _ = s_concl tree in
  mem

let s_control tree =
  let _, _, _, control = s_concl tree in
  control

let b_concl = function
  | BTreeSeq (_, concl) -> concl

let b_output_memory tree =
  let _, _, mem, _ = b_concl tree in
  mem

let b_control tree =
  let _, _, _, control = b_concl tree in
  control

let f_concl = function
  | FTreeReturn (_, concl) | FTreeNoReturn (_, concl) -> concl

let f_output_memory tree =
  let _, _, _, mem, _ = f_concl tree in
  mem

let f_control tree =
  let _, _, _, _, control = f_concl tree in
  control

let p_concl = function
  | PTreeMainReturn (_, concl) -> concl

let p_output_memory tree =
  let _, mem, _ = p_concl tree in
  mem

let p_value tree =
  let _, _, value = p_concl tree in
  value
