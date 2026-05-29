open Language
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
  let is_top aval = equal aval top
  let singleton = Itv.singleton
  let string_of_t = Itv.string_of_t
end

module Abs_env = struct
  type t = Mem of Abs_val.t Loc.Map.t | Bot

  let empty : t = Mem Loc.Map.empty
  let default_val = Itv.singleton 0

  let aval_or_default = function Some aval -> aval | None -> default_val

  let keep_non_default aval =
    if Itv.equal aval default_val then None else Some aval

  let find loc aenv =
    match aenv with
    | Bot -> Itv.Bot
    | Mem bindings -> (
        match Loc.Map.find_opt loc bindings with
        | Some aval -> aval
        | None -> default_val (* default value for uninitialized variables *))

  let string_of_t aenv =
    match aenv with
    | Bot -> "⟂"
    | Mem bindings ->
        let f k aval (acc, first) =
          let semicolon = if first then "" else "; " in
          (acc ^ semicolon ^ k ^ " |-> " ^ Itv.string_of_t aval, false)
        in
        fst (Loc.Map.fold f bindings ("[", true)) ^ "]"

  let add loc aval aenv =
    match aenv with
    | Bot -> Bot
    | Mem bindings ->
        if Itv.equal aval Itv.Bot then Bot
        else
          (* Canonicalize the implicit [0,0] default so fixpoint checks do not
             oscillate between absent keys and explicit default bindings. *)
          Mem
            (if Itv.equal aval default_val then Loc.Map.remove loc bindings
             else Loc.Map.add loc aval bindings)

  let of_concrete_env (cenv : Environment.t) : t =
    Environment.VarMap.fold
      (fun x cval aenv -> add x (Abs_val.singleton cval) aenv)
      cenv empty

  let leq aenv1 aenv2 =
    match (aenv1, aenv2) with
    | Bot, _ -> true
    | _, Bot -> false
    | Mem bindings1, Mem bindings2 ->
        Loc.Map.is_empty
          (Loc.Map.merge
             (fun _ aval1_opt aval2_opt ->
               let aval1 = aval_or_default aval1_opt in
               let aval2 = aval_or_default aval2_opt in
               if Itv.(aval1 <= aval2) then None else Some ())
             bindings1 bindings2)

  let equal aenv1 aenv2 = leq aenv1 aenv2 && leq aenv2 aenv1

  let join aenv1 aenv2 =
    match (aenv1, aenv2) with
    | Bot, m | m, Bot -> m
    | Mem bindings1, Mem bindings2 ->
        Mem
          (Loc.Map.merge
             (fun _ aval1_opt aval2_opt ->
               keep_non_default
                 (Itv.join
                    (aval_or_default aval1_opt)
                    (aval_or_default aval2_opt)))
             bindings1 bindings2)

  let widen old_aenv new_aenv =
    match (old_aenv, new_aenv) with
    | Bot, m | m, Bot -> m
    | Mem old_bindings, Mem new_bindings ->
        let widen_val old_aval new_aval = Itv.widen old_aval new_aval in
        Mem
          (Loc.Map.merge
             (fun _ old_aval_opt new_aval_opt ->
               keep_non_default
                 (widen_val
                    (aval_or_default old_aval_opt)
                    (aval_or_default new_aval_opt)))
             old_bindings new_bindings)
end

module Abs_sem = struct
  type t = Abs_env.t Cmd.Lbl_map.t

  let string_of_t sem =
    Cmd.Lbl_map.fold
      (fun lbl aenv acc ->
        let semicolon = if acc = "" then "" else "\n" in
        acc ^ semicolon
        ^ Cmd.Lbl_map.string_of_key lbl
        ^ " |-> " ^ Abs_env.string_of_t aenv)
      sem ""
end
