open Language.Syntax

module Abs_env = Abs_domain.Abs_env

let rec filter_t e aenv =
  if not (Itv.maybe_true (Eval.antp_exp aenv e)) then Abs_env.Bot
  else
    Exp.(
      match e with
      | Bop (op, e1, e2) -> (
        match op with
        | Eq -> (
            let aval1 = Eval.antp_exp aenv e1 in
            let aval2 = Eval.antp_exp aenv e2 in
            let new_aval = Itv.meet aval1 aval2 in
            match (e1, e2) with
            | Var x, Var y -> Abs_env.add x new_aval (Abs_env.add y new_aval aenv)
            | Var x, _ | _, Var x -> Abs_env.add x new_aval aenv
            | _, _ -> aenv (* 포기 *))
        | Lt -> (
            let aval1 = Eval.antp_exp aenv e1 in
            let aval2 = Eval.antp_exp aenv e2 in
            match (e1, e2) with
            | Var x, Var y ->
                (* x < y 이므로, x는 aval2보다 작아야 하고 y는 aval1보다 커야 함 *)
                let new_aval_x = Itv.filter_lt aval2 (Abs_env.find x aenv) in
                let new_aval_y = Itv.filter_gt aval1 (Abs_env.find y aenv) in
                aenv |> Abs_env.add x new_aval_x |> Abs_env.add y new_aval_y
            | Var x, _ ->
                let new_aval_x = Itv.filter_lt aval2 (Abs_env.find x aenv) in
                Abs_env.add x new_aval_x aenv
            | _, Var x ->
                let new_aval_x = Itv.filter_gt aval1 (Abs_env.find x aenv) in
                Abs_env.add x new_aval_x aenv
            | _ -> aenv)
        | Gt -> filter_t (Bop (Lt, e2, e1)) aenv
        | Ne -> (
            let aval1 = Eval.antp_exp aenv e1 in
            let aval2 = Eval.antp_exp aenv e2 in
            match (e1, e2) with
            | Var x, Var y ->
                let new_aval_x = Itv.filter_ne aval2 (Abs_env.find x aenv) in
                let new_aval_y = Itv.filter_ne aval1 (Abs_env.find y aenv) in
                aenv |> Abs_env.add x new_aval_x |> Abs_env.add y new_aval_y
            | Var x, _ ->
                let new_aval_x = Itv.filter_ne aval2 (Abs_env.find x aenv) in
                Abs_env.add x new_aval_x aenv
            | _, Var x ->
                let new_aval_x = Itv.filter_ne aval1 (Abs_env.find x aenv) in
                Abs_env.add x new_aval_x aenv
            | _ -> aenv)
        | Le -> (
            let aval1 = Eval.antp_exp aenv e1 in
            let aval2 = Eval.antp_exp aenv e2 in
            match (e1, e2) with
            | Var x, Var y ->
                (* x <= y 이므로, x는 aval2보다 작아야 하고 y는 aval1보다 커야 함 *)
                let new_aval_x = Itv.filter_le aval2 (Abs_env.find x aenv) in
                let new_aval_y = Itv.filter_ge aval1 (Abs_env.find y aenv) in
                aenv |> Abs_env.add x new_aval_x |> Abs_env.add y new_aval_y
            | Var x, _ ->
                let new_aval_x = Itv.filter_le aval2 (Abs_env.find x aenv) in
                Abs_env.add x new_aval_x aenv
            | _, Var x ->
                let new_aval_x = Itv.filter_ge aval1 (Abs_env.find x aenv) in
                Abs_env.add x new_aval_x aenv
            | _ -> aenv)
        | Ge -> filter_t (Bop (Le, e2, e1)) aenv
        | _ -> aenv (* 잘 정의되지 않음 *))
      | _ -> aenv (* 포기 *))

let filter_f e aenv =
  if not (Itv.maybe_false (Eval.antp_exp aenv e)) then Abs_env.Bot
  else
    Exp.(
      match e with
      | Bop (op, e1, e2) -> (
        match op with
        | Eq -> filter_t (Bop (Ne, e1, e2)) aenv
        | Lt -> filter_t (Bop (Ge, e1, e2)) aenv
        | Gt -> filter_t (Bop (Le, e1, e2)) aenv
        | Ne -> filter_t (Bop (Eq, e1, e2)) aenv
        | Le -> filter_t (Bop (Gt, e1, e2)) aenv
        | Ge -> filter_t (Bop (Lt, e1, e2)) aenv
        | _ -> aenv (* non-relational operators do not affect the memory *))
      | _ -> aenv (* non-relational expressions do not affect the memory *))
