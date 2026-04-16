(*
 * SNU 4190.664A Static Program Analysis
 * 2025 Jay Lee <jhlee@ropas.snu.ac.kr>, <jaeho.lee@snu.ac.kr>
 *)

open Language.Syntax

module Loc = struct
  type t = Exp.id

  module Map = Map.Make (struct
    type nonrec t = t

    let compare = String.compare
  end)
end

module Abs_val = struct
  type t = Itv.t

  let compare = Stdlib.compare
  let equal = Itv.equal
  let top = Itv.top
  let is_top v = equal v top
  let string_of_t = Itv.string_of_t
end

module Abs_mem = struct
  type t = Mem of Abs_val.t Loc.Map.t | Bot

  let empty : t = Mem Loc.Map.empty

  let find loc mem =
    match mem with
    | Bot -> Itv.Bot
    | Mem m -> (
        match Loc.Map.find_opt loc m with
        | Some v -> v
        | None ->
            Itv.singleton 0 (* default value for uninitialized variables *))

  let string_of_t mem =
    match mem with
    | Bot -> "⟂"
    | Mem m ->
        let f k v (acc, first) =
          let semicolon = if first then "" else "; " in
          (acc ^ semicolon ^ k ^ " |-> " ^ Itv.string_of_t v, false)
        in
        fst (Loc.Map.fold f m ("[", true)) ^ "]"

  let add loc v mem =
    match mem with
    | Bot -> Mem (Loc.Map.singleton loc v)
    | Mem m -> Mem (Loc.Map.add loc v m)

  let equal m1 m2 =
    match (m1, m2) with
    | Bot, Bot -> true
    | Mem m1, Mem m2 -> Loc.Map.equal Itv.equal m1 m2
    | _ -> false

  let widen m_old m_new =
    match (m_old, m_new) with
    | Bot, m | m, Bot -> m
    | Mem old, Mem new_ ->
        let widen_val v_old v_new = Itv.widen v_old v_new in
        Mem
          (Loc.Map.merge
             (fun _ v_old_opt v_new_opt ->
               match (v_old_opt, v_new_opt) with
               | None, None -> None
               | Some v_old, None -> Some v_old
               | None, Some v_new -> Some v_new
               | Some v_old, Some v_new -> Some (widen_val v_old v_new))
             old new_)

  (* module Set = struct include Set.Make (struct type nonrec t = t

     let compare = Loc.Map.compare Abs_val.compare end)

     let string_of_t ms = let f v (acc, first) = let comma = if first then "\n "
     else ",\n " in (acc ^ comma ^ string_of_t v, false) in let ret, first =
     fold f ms ("{", true) in if first then ret ^ "}" else ret ^ "\n}" end *)
end

module Abs_sem = struct
  type t = Abs_mem.t Cmd.Lbl_map.t

  let string_of_t sem =
    Cmd.Lbl_map.fold
      (fun lbl mem acc ->
        let semicolon = if acc = "" then "" else "\n" in
        acc ^ semicolon
        ^ Cmd.Lbl_map.string_of_key lbl
        ^ " |-> " ^ Abs_mem.string_of_t mem)
      sem ""
end

let rec antp_exp (m : Abs_mem.t) : Exp.t -> Abs_val.t = function
  | Int n -> Itv.singleton n
  | Var x -> Abs_mem.find x m
  | Bop (op, e1, e2) ->
      let v1 = antp_exp m e1 in
      let v2 = antp_exp m e2 in
      Itv.bop op v1 v2
  | Uop (op, e) ->
      let v = antp_exp m e in
      Itv.uop op v

let rec filter_t e mem =
  Exp.(
    match e with
    | Bop (op, e1, e2) -> (
        match op with
        | Eq -> (
            let v1 = antp_exp mem e1 in
            let v2 = antp_exp mem e2 in
            let new_v = Itv.meet v1 v2 in
            match (e1, e2) with
            | Var x, Var y -> Abs_mem.add x new_v (Abs_mem.add y new_v mem)
            | Var x, _ | _, Var x -> Abs_mem.add x new_v mem
            | _, _ -> mem (* 포기 *))
        | Lt -> (
            let v1 = antp_exp mem e1 in
            let v2 = antp_exp mem e2 in
            match (e1, e2) with
            | Var x, Var y ->
                (* x < y 이므로, x는 v2보다 작아야 하고 y는 v1보다 커야 함 *)
                let new_vx = Itv.filter_lt v2 (Abs_mem.find x mem) in
                let new_vy = Itv.filter_gt v1 (Abs_mem.find y mem) in
                mem |> Abs_mem.add x new_vx |> Abs_mem.add y new_vy
            | Var x, _ ->
                let new_vx = Itv.filter_lt v2 (Abs_mem.find x mem) in
                Abs_mem.add x new_vx mem
            | _, Var x ->
                let new_vx = Itv.filter_gt v1 (Abs_mem.find x mem) in
                Abs_mem.add x new_vx mem
            | _ -> mem)
        | Gt -> filter_t (Bop (Lt, e2, e1)) mem
        | Ne -> (
            let v1 = antp_exp mem e1 in
            let v2 = antp_exp mem e2 in
            match (e1, e2) with
            | Var x, Var y ->
                let new_vx = Itv.filter_ne v2 (Abs_mem.find x mem) in
                let new_vy = Itv.filter_ne v1 (Abs_mem.find y mem) in
                mem |> Abs_mem.add x new_vx |> Abs_mem.add y new_vy
            | Var x, _ ->
                let new_vx = Itv.filter_ne v2 (Abs_mem.find x mem) in
                Abs_mem.add x new_vx mem
            | _, Var x ->
                let new_vx = Itv.filter_ne v1 (Abs_mem.find x mem) in
                Abs_mem.add x new_vx mem
            | _ -> mem)
        | Le -> (
            let v1 = antp_exp mem e1 in
            let v2 = antp_exp mem e2 in
            match (e1, e2) with
            | Var x, Var y ->
                (* x <= y 이므로, x는 v2보다 작아야 하고 y는 v1보다 커야 함 *)
                let new_vx = Itv.filter_le v2 (Abs_mem.find x mem) in
                let new_vy = Itv.filter_ge v1 (Abs_mem.find y mem) in
                mem |> Abs_mem.add x new_vx |> Abs_mem.add y new_vy
            | Var x, _ ->
                let new_vx = Itv.filter_le v2 (Abs_mem.find x mem) in
                Abs_mem.add x new_vx mem
            | _, Var x ->
                let new_vx = Itv.filter_ge v1 (Abs_mem.find x mem) in
                Abs_mem.add x new_vx mem
            | _ -> mem)
        | Ge -> filter_t (Bop (Le, e2, e1)) mem
        | _ -> mem (* 잘 정의되지 않음 *))
    | _ -> mem (* 포기 *))

let filter_f e mem =
  Exp.(
    match e with
    | Bop (op, e1, e2) -> (
        match op with
        | Eq -> filter_t (Bop (Ne, e1, e2)) mem
        | Lt -> filter_t (Bop (Ge, e1, e2)) mem
        | Gt -> filter_t (Bop (Le, e1, e2)) mem
        | Ne -> filter_t (Bop (Eq, e1, e2)) mem
        | Le -> filter_t (Bop (Gt, e1, e2)) mem
        | Ge -> filter_t (Bop (Lt, e1, e2)) mem
        | _ -> mem (* non-relational operators do not affect the memory *))
    | _ -> mem (* non-relational expressions do not affect the memory *))

let analysis (prog : Cmd.lbl_t) : Abs_mem.t =
  let prog = Cmd.relabel prog in
  let table = Cmd.tabulate prog in
  let start = 1 in
  let exit = 99 in
  let Cfg.{ next; next_true; next_false } = Cfg.make prog exit in

  let wl = Queue.create () in
  let sem = ref (Cmd.Lbl_map.map (fun _ -> Abs_mem.Bot) table) in
  sem := Cmd.Lbl_map.add start Abs_mem.empty !sem;
  sem := Cmd.Lbl_map.add exit Abs_mem.Bot !sem;

  Queue.push start wl;

  let rec run () =
    if Queue.is_empty wl then ()
    else
      let cur = Queue.pop wl in
      (* print_endline (Abs_sem.string_of_t !sem); *)
      (* print_endline ("Processing label: " ^ Cmd.Lbl_map.string_of_key cur); *)
      if cur = exit then run () (* skip processing the exit label *)
      else
        let cur_mem = Cmd.Lbl_map.find cur !sem in
        let update_list =
          match Cmd.Lbl_map.find cur table with
          | Cmd.Assign (x, e) ->
              let v = antp_exp cur_mem e in
              [
                ( next cur,
                  Abs_mem.Mem
                    (Loc.Map.add x v
                       (match cur_mem with
                       | Abs_mem.Mem m -> m
                       | Abs_mem.Bot -> Loc.Map.empty)) );
              ]
          | Cmd.If (e, _, _) | Cmd.While (e, _) ->
              [
                (next_true cur, filter_t e cur_mem);
                (next_false cur, filter_f e cur_mem);
              ]
          | _ -> [ (next cur, cur_mem) ]
        in
        List.iter
          (fun (nex, mem) ->
            let old_mem = Cmd.Lbl_map.find nex !sem in
            let new_mem = Abs_mem.widen old_mem mem in
            if not (Abs_mem.equal new_mem old_mem) then (
              sem := Cmd.Lbl_map.add nex new_mem !sem;
              Queue.push nex wl))
          update_list;
        run ()
  in
  run ();
  print_endline (Abs_sem.string_of_t !sem);
  !sem |> Cmd.Lbl_map.find exit
