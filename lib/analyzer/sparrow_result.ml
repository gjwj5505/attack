type bound = Neg_inf | Pos_inf | Int of int

type interval = Bot | Interval of bound * bound

type value = {
  itv : interval;
  raw : string;
}

type binding = {
  loc : string;
  value : value;
}

type mem = {
  is_bot : bool;
  bindings : binding list;
}

type node_state = {
  node : string;
  mem : mem;
}

type alarm_summary = {
  total : int;
  proven : int;
  unproven : int;
  bot : int;
}

type analysis = {
  file : string;
  analysis : string;
  main_exit_node : string option;
  alarms : alarm_summary;
  input : node_state list;
  output : node_state list;
}

let bound_le a b =
  match (a, b) with
  | Neg_inf, _ -> true
  | _, Pos_inf -> true
  | Int x, Int y -> x <= y
  | _, _ -> false

let string_of_bound = function
  | Neg_inf -> "-oo"
  | Pos_inf -> "+oo"
  | Int n -> string_of_int n

let string_of_interval = function
  | Bot -> "bot"
  | Interval (lo, hi) ->
      "[" ^ string_of_bound lo ^ ", " ^ string_of_bound hi ^ "]"

let string_of_value value =
  string_of_interval value.itv ^ " raw=" ^ value.raw
