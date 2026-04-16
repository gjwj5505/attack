(*
 * SNU 4190.664A Static Program Analysis
 * 2025 Jay Lee <jhlee@ropas.snu.ac.kr>, <jaeho.lee@snu.ac.kr>
 *)

open Syntax

module Loc = struct
  type t = Exp.id

  module Map = Map.Make (struct
    type nonrec t = t

    let compare = String.compare
  end)
end

module Value = struct
  type t = Int of int

  let compare v1 v2 = match (v1, v2) with Int n1, Int n2 -> Int.compare n1 n2
  let of_int n = Int n
  let string_of_t = function Int n -> string_of_int n
end

module Mem = struct
  type t = Value.t Loc.Map.t

  let empty : t = Loc.Map.empty

  let find loc mem =
    match Loc.Map.find_opt loc mem with Some v -> v | None -> Value.of_int 0

  let string_of_t mem =
    let f k v (acc, first) =
      let semicolon = if first then "" else "; " in
      (acc ^ semicolon ^ k ^ " |-> " ^ Value.string_of_t v, false)
    in
    fst (Loc.Map.fold f mem ("[", true)) ^ "]"

  module Set = struct
    include Set.Make (struct
      type nonrec t = t

      let compare = Loc.Map.compare Value.compare
    end)

    let string_of_t ms =
      let f v (acc, first) =
        let comma = if first then "\n " else ",\n " in
        (acc ^ comma ^ string_of_t v, false)
      in
      let ret, first = fold f ms ("{", true) in
      if first then ret ^ "}" else ret ^ "\n}"
  end
end

exception Type_error of string

let rec intp_exp (m : Mem.t) : Exp.t -> Value.t = function
  | Int n -> Value.Int n
  | Var x -> Mem.find x m
  | Bop (op, e1, e2) -> (
      let v1 = intp_exp m e1 in
      let v2 = intp_exp m e2 in
      match (v1, v2) with
      | Int i1, Int i2 -> (
          match op with
          | Eq -> if i1 = i2 then Int 1 else Int 0
          | Lt -> if i1 < i2 then Int 1 else Int 0
          | Gt -> if i1 > i2 then Int 1 else Int 0
          | Ne -> if i1 <> i2 then Int 1 else Int 0
          | Le -> if i1 <= i2 then Int 1 else Int 0
          | Ge -> if i1 >= i2 then Int 1 else Int 0
          | Plus -> Int (i1 + i2)
          | Minus -> Int (i1 - i2)
          | Times -> Int (i1 * i2)))
  | Uop (op, e) -> (
      let v = intp_exp m e in
      match v with Int n -> ( match op with Uminus -> Int (-n)))

(** Transitional interpreter *)
let trans_intp (prog : Cmd.lbl_t) : Mem.t =
  let prog = Cmd.relabel prog in
  let table = Cmd.tabulate prog in
  (* let exit = Either.Right 0 in *)
  let exit = 0 in
  (* ?? *)
  let Cfg.{ next; next_true; next_false } = Cfg.make prog exit in
  let rec run mem lbl =
    if lbl = exit then mem
    else
      match Cmd.Lbl_map.find lbl table with
      | Assign (x, e) ->
          let v = intp_exp mem e in
          let mem = Loc.Map.add x v mem in
          run mem (next lbl)
      | Seq _ -> run mem (next lbl)
      | If (pred, _, _) -> (
          match intp_exp mem pred with
          | Int i ->
              if i <> 0 then run mem (next_true lbl)
              else run mem (next_false lbl))
      | While (pred, _) -> (
          match intp_exp mem pred with
          | Int i ->
              if i <> 0 then run mem (next_true lbl)
              else run mem (next_false lbl))
  in
  run Mem.empty prog.lbl

(** Definitional interpreter *)
let def_intp (prog : Cmd.lbl_t) : Mem.t =
  let rec run mem : Cmd.t -> Mem.t = function
    | Assign (x, e) ->
        let v = intp_exp mem e in
        Loc.Map.add x v mem
    | Seq (c1, c2) ->
        let mem = run mem c1.cmd in
        run mem c2.cmd
    | If (pred, con, alt) -> (
        match intp_exp mem pred with
        | Int i -> if i <> 0 then run mem con.cmd else run mem alt.cmd)
    | While (pred, c) as whl -> (
        match intp_exp mem pred with
        | Int i -> if i <> 0 then run (run mem c.cmd) whl else mem)
  in
  run Mem.empty prog.cmd
