(*
 * SNU 4190.664A Static Program Analysis
 * Domain functors. See dom_ex.ml for its usage examples.
 *)

module type Elt = sig
  type t

  val compare : t -> t -> int
end

module type Set = sig
  type elt
  type t

  exception Inf

  val cmp_elt : elt -> elt -> int
  val empty : t
  val all : unit -> t
  val to_list : t -> elt list
  val add : elt -> t -> t
  val remove : elt -> t -> t
  val mem : elt -> t -> bool
  val subset : t -> t -> bool
  val union : t -> t -> t
  val inter : t -> t -> t
  val diff : t -> t -> t
  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
end

module type Dom = sig
  type t (* the type of abstract domain elements *)

  val bot : t
  val top : t
  val join : t -> t -> t
  val leq : t -> t -> bool (* leq x y is true if x is less/equal than y *)
end

module Basic_set (A : Elt) = struct
  include Set.Make (A)

  exception Inf

  let cmp_elt = A.compare
  let all () = raise Inf
  let to_list = elements
end

module Product_set (A : Set) (B : Set) = struct
  let cmp_elt (a, b) (a', b') =
    if A.cmp_elt a a' = 0 then B.cmp_elt b b' else A.cmp_elt a a'

  include Set.Make (struct
    type t = A.elt * B.elt

    let compare = cmp_elt
  end)

  exception Inf

  let all =
   fun () ->
    try
      A.fold
        (fun a c -> B.fold (fun b c -> add (a, b) c) (B.all ()) c)
        (A.all ()) empty
    with A.Inf | B.Inf -> raise Inf

  let to_list = elements
end

module FlatDomain (A : Elt) = struct
  type t = Bot | Top | Elt of A.t

  let bot = Bot
  let top = Top

  let join x y =
    match (x, y) with
    | Bot, _ -> y
    | _, Bot -> x
    | Top, _ -> Top
    | _, Top -> Top
    | Elt a, Elt b -> if A.compare a b = 0 then x else Top

  let leq x y =
    match (x, y) with
    | Bot, _ -> true
    | _, Top -> true
    | Top, _ -> false
    | _, Bot -> false
    | Elt a, Elt b -> A.compare a b = 0

  let make a = Elt a
end

module Product_dom (A : Dom) (B : Dom) = struct
  type t = A.t * B.t

  let bot = (A.bot, B.bot)
  let top = (A.top, B.top)

  let join x y =
    let a, b = x in
    let a', b' = y in
    (A.join a a', B.join b b')

  let leq x y =
    let a, b = x in
    let a', b' = y in
    A.leq a a' && B.leq b b'

  let l x = fst x
  let r x = snd x
  let make a b = (a, b)
end

module Power_set_dom (S : Set) = struct
  type t = Top | Elt of S.t

  let bot = Elt S.empty
  let top = Top

  let join x y =
    match (x, y) with
    | Top, _ -> Top
    | _, Top -> Top
    | Elt s, Elt s' -> Elt (S.union s s')

  let mem a s = match s with Top -> true | Elt s -> S.mem a s

  let fold f x a =
    match x with Top -> S.fold f (S.all ()) a | Elt s -> S.fold f s a

  let map f x =
    match x with
    | Top -> Elt (S.fold (fun a s' -> S.add (f a) s') (S.all ()) S.empty)
    | Elt s -> Elt (S.fold (fun a s' -> S.add (f a) s') s S.empty)

  let make lst = Elt (List.fold_left (fun s x -> S.add x s) S.empty lst)

  let leq x y =
    match (x, y) with
    | _, Top -> true
    | Top, Elt s -> ( try S.subset (S.all ()) s with S.Inf -> false)
    | Elt s1, Elt s2 -> S.subset s1 s2

  let union x y =
    match (x, y) with
    | Top, _ -> Top
    | _, Top -> Top
    | Elt s1, Elt s2 -> Elt (S.union s1 s2)

  let inter x y =
    match (x, y) with
    | Top, _ -> y
    | _, Top -> x
    | Elt s1, Elt s2 -> Elt (S.inter s1 s2)

  let diff x y =
    match (x, y) with
    | Top, Elt s1 -> Elt (S.diff (S.all ()) s1)
    | _, Top -> Elt S.empty
    | Elt s1, Elt s2 -> Elt (S.diff s1 s2)

  let remove a x =
    match x with
    | Elt s -> Elt (S.remove a s)
    | Top -> Elt (S.remove a (S.all ()))

  let to_list x =
    match x with Top -> S.to_list (S.all ()) | Elt s -> S.to_list s
end

module Fun_dom_from_set (A : Set) (B : Dom) = struct
  module Map = Map.Make (struct
    type t = A.elt

    let compare = A.cmp_elt
  end)

  type t = Top | Elt of B.t Map.t

  let bot = Elt Map.empty
  let top = Top

  let join x y =
    match (x, y) with
    | Top, _ -> Top
    | _, Top -> Top
    | Elt m1, Elt m2 ->
        Elt
          (Map.fold
             (fun k v acc_m ->
               if Map.mem k acc_m then
                 Map.add k (B.join v (Map.find k acc_m)) acc_m
               else Map.add k v acc_m)
             m1 m2)

  let leq x y =
    match (x, y) with
    | _, Top -> true
    | Top, Elt s -> (
        try
          A.fold
            (fun e a ->
              if Map.mem e s then B.leq B.top (Map.find e s) && a else false)
            (A.all ()) true
        with A.Inf -> false)
    | Elt s1, Elt s2 ->
        Map.fold
          (fun k a b ->
            if Map.mem k s2 then B.leq a (Map.find k s2) && b
            else B.leq a B.bot && b)
          s1 true

  let image x l =
    match x with
    | Top -> B.top
    | Elt s -> if Map.mem l s then Map.find l s else B.bot

  let update x l r =
    match x with
    | Top ->
        if B.leq B.top r then Top
        else
          Elt
            (A.fold
               (fun e a ->
                 if A.cmp_elt e l = 0 then Map.add e r a else Map.add e B.top a)
               (A.all ()) Map.empty)
    | Elt s -> Elt (Map.add l r s)

  let weak_update x l r =
    match x with
    | Top -> Top
    | Elt s ->
        if Map.mem l s then Elt (Map.add l (B.join r (Map.find l s)) s)
        else Elt (Map.add l r s)

  let map f x =
    match x with
    | Top ->
        Elt
          (A.fold
             (fun l a ->
               let l', r' = f l B.top in
               Map.add l' r' a)
             (A.all ()) Map.empty)
    | Elt s ->
        Elt
          (Map.fold
             (fun l r a ->
               let l', r' = f l r in
               Map.add l' r' a)
             s Map.empty)

  let fold f x acc =
    match x with
    | Top -> A.fold (fun l a -> f l B.top a) (A.all ()) acc
    | Elt s -> Map.fold (fun l r a -> f l r a) s acc

  let to_list x =
    match x with
    | Top -> List.map (fun l -> (l, B.top)) (A.to_list (A.all ()))
    | Elt s -> Map.bindings s

  let make l = Elt (List.fold_left (fun a (b, c) -> Map.add b c a) Map.empty l)
end

module Fun_dom (A : Elt) (B : Dom) = struct
  module S = Basic_set (A)
  include Fun_dom_from_set (S) (B)
end
