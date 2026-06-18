open BigStep

let is_normal = function
  | Normal -> true
  | _ -> false

let is_return = function
  | Return _ -> true
  | _ -> false

let is_break = function
  | Break -> true
  | _ -> false

let is_continue = function
  | Continue -> true
  | _ -> false

let return_value = function
  | Return value -> Some value
  | Normal | Break | Continue -> None

let string_of_control = function
  | Normal -> "Normal"
  | Return value -> "Return(" ^ Value.string_of_t value ^ ")"
  | Break -> "Break"
  | Continue -> "Continue"

let get_e_concl = function
  | EIntLiteral (_, c)
  | ENegIntLiteral (_, c)
  | ELval (_, c)
  | EBop (_, c)
  | EUop (_, c)
  | ELogicalOrLeftTrue (_, c)
  | ELogicalOrLeftFalse (_, c)
  | ELogicalAndLeftFalse (_, c)
  | ELogicalAndLeftTrue (_, c) ->
      c

let get_s_concl = function
  | SDecl (_, c)
  | SAssign (_, c)
  | SIfTrue (_, c)
  | SIfFalse (_, c)
  | SWhileFalse (_, c)
  | SWhileTrueNormal (_, c)
  | SWhileTrueContinue (_, c)
  | SWhileTrueBreak (_, c)
  | SWhileTrueReturn (_, c)
  | SReturn (_, c) ->
      c

let get_b_concl = function
  | BEmpty c
  | BSeqNormal (_, c)
  | BSeqReturn (_, c)
  | BSeqBreak (_, c)
  | BSeqContinue (_, c) ->
      c

let get_p_concl = function
  | PMainReturn (_, c) -> c

let get_e_concl_output_memory ((_, _, mem, _) : e_concl) = mem
let get_e_concl_value ((_, _, _, value) : e_concl) = value
let get_s_concl_output_memory ((_, _, mem, _) : s_concl) = mem
let get_s_concl_control ((_, _, _, control) : s_concl) = control
let get_b_concl_output_memory ((_, _, mem, _) : b_concl) = mem
let get_b_concl_control ((_, _, _, control) : b_concl) = control

let get_e_output_memory tree = get_e_concl_output_memory (get_e_concl tree)
let get_e_value tree = get_e_concl_value (get_e_concl tree)
let get_s_output_memory tree = get_s_concl_output_memory (get_s_concl tree)
let get_s_control tree = get_s_concl_control (get_s_concl tree)
let get_b_output_memory tree = get_b_concl_output_memory (get_b_concl tree)
let get_b_control tree = get_b_concl_control (get_b_concl tree)
