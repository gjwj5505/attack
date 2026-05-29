open Language

module type ENGINE = sig
  type aval
  type aenv
  type sem

  val analysis : ?init_cenv:Environment.t -> Syntax.Cmd.lbl_t -> aenv
  val analysis_sem : ?init_cenv:Environment.t -> Syntax.Cmd.lbl_t -> sem
  val exit_aenv : sem -> aenv
  val find : string -> aenv -> aval
  val contains_concrete : int -> aval -> bool
  val is_singleton : int -> aval -> bool
  val is_top : aval -> bool
  val is_unbounded : aval -> bool
  val string_of_aval : aval -> string
  val string_of_aenv : aenv -> string
  val print_analysis_sem : sem -> Syntax.Cmd.lbl_t -> unit
end

type t = Pack : (module ENGINE) -> t

type aval = Aval : (module ENGINE with type aval = 'a) * 'a -> aval

type aenv = Aenv : (module ENGINE with type aenv = 'e) * 'e -> aenv

type sem = Sem : (module ENGINE with type sem = 's) * 's -> sem

let analyzer_260417 = Pack (module Engine.V260417.Analyzer : ENGINE)

let analyzer_260528 = Pack (module Engine.V260528.Analyzer : ENGINE)

let default = analyzer_260528

let names () = "260417|260528"

let of_name = function
  | "260417" -> Some analyzer_260417
  | "260528" -> Some analyzer_260528
  | _ -> None

let analysis_sem (Pack (module E)) ?init_cenv pgm =
  Sem ((module E), E.analysis_sem ?init_cenv pgm)

let analysis (Pack (module E)) ?init_cenv pgm =
  Aenv ((module E), E.analysis ?init_cenv pgm)

let exit_aenv (Sem ((module E), sem)) = Aenv ((module E), E.exit_aenv sem)

let find var (Aenv ((module E), aenv)) = Aval ((module E), E.find var aenv)

let contains_concrete cval (Aval ((module E), aval)) =
  E.contains_concrete cval aval

let is_singleton cval (Aval ((module E), aval)) = E.is_singleton cval aval

let is_top (Aval ((module E), aval)) = E.is_top aval

let is_unbounded (Aval ((module E), aval)) = E.is_unbounded aval

let string_of_aval (Aval ((module E), aval)) = E.string_of_aval aval

let string_of_aenv (Aenv ((module E), aenv)) = E.string_of_aenv aenv

let print_analysis_sem (Sem ((module E), sem)) pgm =
  E.print_analysis_sem sem pgm
