(*
 * SNU 4190.664A Static Program Analysis
 * 2025 Jay Lee <jhlee@ropas.snu.ac.kr>, <jaeho.lee@snu.ac.kr>
 *)

module Exp = struct
  type id = string
  type uop = Uminus
  type bop = Eq | Lt | Gt | Ne | Le | Ge | Plus | Minus | Times

  type t =
    | Int of int
    | Var of id
    | Bop of bop * t * t
    | Uop of uop * t

  let string_of_uop : uop -> string = function Uminus -> "-"

  let string_of_bop : bop -> string = function
    | Eq -> "="
    | Lt -> "<"
    | Gt -> ">"
    | Ne -> "<>"
    | Le -> "<="
    | Ge -> ">="
    | Plus -> "+"
    | Minus -> "-"
    | Times -> "*"

  let rec string_of_t : t -> string = function
    | Var id -> id
    | Int n -> string_of_int n
    | Bop (op, e1, e2) ->
        Printf.sprintf "(%s %s %s)" (string_of_t e1) (string_of_bop op)
          (string_of_t e2)
    | Uop (op, e) -> Printf.sprintf "(%s %s)" (string_of_uop op) (string_of_t e)
end

module Cmd = struct
  type lbl_t = { lbl : int; cmd : t }
  and lbl = int
  and t =
    | Assign of string * Exp.t
    | Seq of lbl_t * lbl_t
    | If of Exp.t * lbl_t * lbl_t
    | While of Exp.t * lbl_t

  module Lbl_map = struct
    include Map.Make (struct
      type t = int

      let compare = Int.compare
    end)

    let string_of_key : key -> string = function
      | lbl -> Printf.sprintf "[L]%3d" lbl (* normal [L]abel *)
  end

  let tabulate (l_cmd : lbl_t) : t Lbl_map.t =
    let rec tabulate' { lbl; cmd } tbl =
      let tbl = Lbl_map.add lbl cmd tbl in
      match cmd with
      | Seq (c1, c2) -> tbl |> tabulate' c1 |> tabulate' c2
      | If (_, c1, c2) -> tbl |> tabulate' c1 |> tabulate' c2
      | While (_, c) ->
          tbl |> tabulate' c
      | _ -> tbl
    in
    tabulate' l_cmd Lbl_map.empty

  let relabel (lc : lbl_t) : lbl_t =
    let rec relabel' lbl { cmd; _ } =
      let lbl = lbl + 1 in
      let cmd, lbl' =
        match cmd with
        | Seq (c1, c2) ->
            let c1, lbl = relabel' lbl c1 in
            let c2, lbl = relabel' lbl c2 in
            (Seq (c1, c2), lbl)
        | If (pred, con, alt) ->
            let con, lbl = relabel' lbl con in
            let alt, lbl = relabel' lbl alt in
            (If (pred, con, alt), lbl)
        | While (pred, c) ->
            let c, lbl = relabel' lbl c in
            (While (pred, c), lbl)
        | cmd -> (cmd, lbl)
      in
      ({ lbl; cmd }, lbl')
    in
    fst @@ relabel' 0 lc

  let indent (lvl : int) (f : 'a -> string) : 'a -> string =
   fun x -> String.init (2 * lvl) (fun _ -> ' ') ^ f x

  let string_of_lb : lbl -> string = fun lbl ->
    string_of_int lbl

  let rec string_of_t ?(lvl : int = 0) : t -> string =
    indent lvl @@ function
    | Assign (id, e) -> Printf.sprintf "%s := %s" id (Exp.string_of_t e)
    | Seq (c1, c2) ->
        (* let lvl = lvl + 1 in *)
        Printf.sprintf "\n%s;\n%s" (string_of_lbl_t ~lvl c1)
          (string_of_lbl_t ~lvl c2)
    | If (pred, con, alt) ->
        let lvl = lvl + 1 in
        Printf.sprintf "if %s then\n%s else\n%s" (Exp.string_of_t pred)
          (string_of_lbl_t ~lvl con) (string_of_lbl_t ~lvl alt)
    | While (pred, c) ->
        Printf.sprintf "while %s\n%s" (Exp.string_of_t pred) (string_of_lbl_t ~lvl:(lvl + 1) c)

  and string_of_lbl_t ?(lvl : int = 0) { lbl; cmd } =
    Printf.sprintf "%3d: %s" lbl (string_of_t ~lvl cmd)

  let rec string_of_nolabel_t ?(lvl : int = 0) : t -> string =
    indent lvl @@ function
    | Assign (id, e) -> Printf.sprintf "%s := %s" id (Exp.string_of_t e)
    | Seq (c1, c2) ->
        Printf.sprintf "\n%s;\n%s" (string_of_nolabel_t ~lvl c1.cmd)
          (string_of_nolabel_t ~lvl c2.cmd)
    | If (pred, con, alt) ->
        let lvl = lvl + 1 in
        Printf.sprintf "if %s then\n%s else\n%s" (Exp.string_of_t pred)
          (string_of_nolabel_t ~lvl con.cmd)
          (string_of_nolabel_t ~lvl alt.cmd)
    | While (pred, c) ->
        Printf.sprintf "while %s\n%s" (Exp.string_of_t pred)
          (string_of_nolabel_t ~lvl:(lvl + 1) c.cmd)
end

module Cfg = struct
  type t = Cmd.lbl -> Cmd.lbl

  exception End_of_cfg

  let empty : t = fun _ -> raise End_of_cfg

  let bind (cfg : t) (lbl : Cmd.lbl) (next : Cmd.lbl) : t =
   fun l -> if l = lbl then next else cfg l

  let ( @+ ) cfg (l, next) = bind cfg l next

  type static_flow = { next : t; next_true : t; next_false : t }

  let make (lc : Cmd.lbl_t) (exit : Cmd.lbl) : static_flow =
    let rec make' Cmd.{ cmd = c; lbl = l } exit
        ({ next; next_true; next_false } as cfg) =
      match c with
      | Assign _ -> { cfg with next = next @+ (l, exit) }
      | Seq (c1, c2) ->
          { cfg with next = next @+ (l, c1.lbl) }
          |> make' c1 (c2.lbl) |> make' c2 exit
      | If (_, c1, c2) ->
          {
            cfg with
            next_true = next_true @+ (l, c1.lbl);
            next_false = next_false @+ (l, c2.lbl);
          }
          |> make' c1 exit |> make' c2 exit
      | While (_, c) ->
          {
            cfg with
            next_true = next_true @+ (l, c.lbl);
            next_false = next_false @+ (l, exit);
          }
          |> make' c l
    in
    make' lc exit { next = empty; next_true = empty; next_false = empty }
end
