open Language

type t = {
  vars : string list;
  target_var : string;
  ints : int list;
  value_range : int * int;
  uops : Syntax.Exp.uop list;
  bops : Syntax.Exp.bop list;
  heuristic_name : string;
  analyzer_name : string;
  seed : int;
}

let vars = [ "x" (*; "y"*) ]
let target_var = "x"

let ints = [ -1; 0; 1 ]

let value_range = (0, 4)

let uops = Syntax.Exp.[ Uminus ]

let bops =
  Syntax.Exp.
    [
      Lt; Plus; Eq; Ne; Times;
      (* Gt; Le; Ge; Minus *)
      (* Gt Ge는 (거의) 필요 없음 *)
    ]

let heuristic_name = "my"

let analyzer_name = "260528"

let seed = 42
