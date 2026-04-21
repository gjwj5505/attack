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
  let default_val = Itv.singleton 0

  let value_or_default = function Some v -> v | None -> default_val

  let keep_non_default v =
    if Itv.equal v default_val then None else Some v

  let find loc mem =
    match mem with
    | Bot -> Itv.Bot
    | Mem m -> (
        match Loc.Map.find_opt loc m with
        | Some v -> v
        | None -> default_val (* default value for uninitialized variables *))

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
    | Bot -> Bot
    | Mem m ->
        if Itv.equal v Itv.Bot then Bot
        else
          (* Canonicalize the implicit [0,0] default so fixpoint checks do not
             oscillate between absent keys and explicit default bindings. *)
          Mem
            (if Itv.equal v default_val then Loc.Map.remove loc m
             else Loc.Map.add loc v m)

  let leq m1 m2 =
    match (m1, m2) with
    | Bot, _ -> true
    | _, Bot -> false
    | Mem m1, Mem m2 ->
        Loc.Map.is_empty
          (Loc.Map.merge
             (fun _ v1 v2 ->
               let v1 = value_or_default v1 in
               let v2 = value_or_default v2 in
               if Itv.(v1 <= v2) then None else Some ())
             m1 m2)

  let equal m1 m2 = leq m1 m2 && leq m2 m1

  let join m1 m2 =
    match (m1, m2) with
    | Bot, m | m, Bot -> m
    | Mem m1, Mem m2 ->
        Mem
          (Loc.Map.merge
             (fun _ v1 v2 ->
               keep_non_default
                 (Itv.join (value_or_default v1) (value_or_default v2)))
             m1 m2)

  let widen m_old m_new =
    match (m_old, m_new) with
    | Bot, m | m, Bot -> m
    | Mem old, Mem new_ ->
        let widen_val v_old v_new = Itv.widen v_old v_new in
        Mem
          (Loc.Map.merge
             (fun _ v_old_opt v_new_opt ->
               keep_non_default
                 (widen_val
                    (value_or_default v_old_opt)
                    (value_or_default v_new_opt)))
             old new_)
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
