open Language.Syntax

module Abs_mem = Abs_domain.Abs_mem

let rec filter_t e mem =
  if not (Itv.maybe_true (Eval.antp_exp mem e)) then Abs_mem.Bot
  else
    Exp.(
      match e with
      | Bop (op, e1, e2) -> (
        match op with
        | Eq -> (
            let v1 = Eval.antp_exp mem e1 in
            let v2 = Eval.antp_exp mem e2 in
            let new_v = Itv.meet v1 v2 in
            match (e1, e2) with
            | Var x, Var y -> Abs_mem.add x new_v (Abs_mem.add y new_v mem)
            | Var x, _ | _, Var x -> Abs_mem.add x new_v mem
            | _, _ -> mem (* 포기 *))
        | Lt -> (
            let v1 = Eval.antp_exp mem e1 in
            let v2 = Eval.antp_exp mem e2 in
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
            let v1 = Eval.antp_exp mem e1 in
            let v2 = Eval.antp_exp mem e2 in
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
            let v1 = Eval.antp_exp mem e1 in
            let v2 = Eval.antp_exp mem e2 in
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
  if not (Itv.maybe_false (Eval.antp_exp mem e)) then Abs_mem.Bot
  else
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
