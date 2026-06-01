open Language
open Component

module type Component = sig
  type payload
  type t

  val make : payload -> t
  val payload : t -> payload
  val score : t -> float
end

module Make_payload_set (C : Component) = struct
  module Internal = Set.Make (struct
    type t = C.t

    let compare left right = Stdlib.compare (C.payload left) (C.payload right)
  end)

  type t = Internal.t
  type elt = C.payload

  let empty = Internal.empty
  let is_empty = Internal.is_empty
  let cardinal = Internal.cardinal
  let add payload set = Internal.add (C.make payload) set
  let remove payload set = Internal.remove (C.make payload) set
  let mem payload set = Internal.mem (C.make payload) set
  let union = Internal.union
  let inter = Internal.inter
  let diff = Internal.diff
  let elements set = set |> Internal.elements |> List.map C.payload
  let iter f set = Internal.iter (fun component -> f (C.payload component)) set
  let fold f set acc =
    Internal.fold (fun component acc -> f (C.payload component) acc) set acc
  let filter p set =
    Internal.filter (fun component -> p (C.payload component)) set
  let for_all p set =
    Internal.for_all (fun component -> p (C.payload component)) set

  let scored_elements set =
    set |> Internal.elements
    |> List.map (fun component -> (C.payload component, C.score component))

  let trim_with_heuristic set =
    set |> Internal.elements
    |> List.map (fun component -> (component, C.score component))
    |> Heuristic.trim_current
    |> List.fold_left
         (fun acc (component, _score) -> Internal.add component acc)
         Internal.empty
end

module ExpSet = Make_payload_set (Exp_component)
module CmdSet = Make_payload_set (Cmd_component)
module ETreeSet = Make_payload_set (Etree_component)
module CTreeSet = Make_payload_set (Ctree_component)

type bucket = {
  exps : ExpSet.t;
  cmds : CmdSet.t;
  etrees : ETreeSet.t;
  ctrees : CTreeSet.t;
}

type t = bucket Size.Map.t

let empty_bucket =
  {
    exps = ExpSet.empty;
    cmds = CmdSet.empty;
    etrees = ETreeSet.empty;
    ctrees = CTreeSet.empty;
  }

let empty = Size.Map.empty

let get_bucket bucket_size tbl =
  match Size.Map.find_opt bucket_size tbl with
  | Some b -> b
  | None -> empty_bucket

let update_bucket bucket_size f tbl =
  let bucket = get_bucket bucket_size tbl in
  Size.Map.add bucket_size (f bucket) tbl

let add_exp bucket_size exp tbl =
  update_bucket bucket_size
    (fun b -> { b with exps = ExpSet.add exp b.exps })
    tbl

let add_cmd bucket_size cmd tbl =
  update_bucket bucket_size
    (fun b -> { b with cmds = CmdSet.add cmd b.cmds })
    tbl

let add_etree bucket_size etree tbl =
  update_bucket bucket_size
    (fun b -> { b with etrees = ETreeSet.add etree b.etrees })
    tbl

let add_ctree bucket_size ctree tbl =
  update_bucket bucket_size
    (fun b -> { b with ctrees = CTreeSet.add ctree b.ctrees })
    tbl

let add_exp_exact e tbl =
  let bucket_size = Size.make (Size.sizeof_Exp e) 0 in
  add_exp bucket_size e tbl

let add_cmd_exact c tbl =
  let bucket_size = Size.make (Size.sizeof_Cmd c) 0 in
  add_cmd bucket_size c tbl

let add_etree_exact et tbl = add_etree (Size.sizeof_etree et) et tbl
let add_ctree_exact ct tbl = add_ctree (Size.sizeof_ctree ct) ct tbl
let exps_of_size size tbl = (get_bucket size tbl).exps
let cmds_of_size size tbl = (get_bucket size tbl).cmds
let etrees_of_size size tbl = (get_bucket size tbl).etrees
let ctrees_of_size size tbl = (get_bucket size tbl).ctrees

let fold_exps size tbl f acc =
  ExpSet.fold f (exps_of_size size tbl) acc

let fold_cmds size tbl f acc =
  CmdSet.fold f (cmds_of_size size tbl) acc

let fold_etrees size tbl f acc =
  ETreeSet.fold f (etrees_of_size size tbl) acc

let fold_ctrees size tbl f acc =
  CTreeSet.fold f (ctrees_of_size size tbl) acc

let trim_size_with_heuristic size tbl =
  match Size.Map.find_opt size tbl with
  | None -> tbl
  | Some _ ->
      let bucket = get_bucket size tbl in
      let exps = ExpSet.trim_with_heuristic bucket.exps in
      let cmds = CmdSet.trim_with_heuristic bucket.cmds in
      let etrees = ETreeSet.trim_with_heuristic bucket.etrees in
      let ctrees = CTreeSet.trim_with_heuristic bucket.ctrees in
      update_bucket size
        (fun _ ->
          { exps; cmds; etrees; ctrees })
        tbl

let exp_elements = ExpSet.elements

let cmd_elements = CmdSet.elements

let etree_elements = ETreeSet.elements

let ctree_elements = CTreeSet.elements

let scored_exp_elements size tbl = ExpSet.scored_elements (exps_of_size size tbl)

let scored_cmd_elements size tbl = CmdSet.scored_elements (cmds_of_size size tbl)

let scored_etree_elements size tbl =
  ETreeSet.scored_elements (etrees_of_size size tbl)

let scored_ctree_elements size tbl =
  CTreeSet.scored_elements (ctrees_of_size size tbl)

let contains_exp = ExpSet.mem
let contains_cmd = CmdSet.mem
let contains_etree = ETreeSet.mem
let contains_ctree = CTreeSet.mem

let fold_sizes f tbl init = Size.Map.fold f tbl init

let bucket_cardinal b =
  ExpSet.cardinal b.exps + CmdSet.cardinal b.cmds + ETreeSet.cardinal b.etrees
  + CTreeSet.cardinal b.ctrees

let string_of_bucket b =
  Printf.sprintf "{exp=%d; cmd=%d; etree=%d; ctree=%d}" (ExpSet.cardinal b.exps)
    (CmdSet.cardinal b.cmds)
    (ETreeSet.cardinal b.etrees)
    (CTreeSet.cardinal b.ctrees)

let string_of_table tbl =
  fold_sizes
    (fun size bucket acc ->
      if bucket_cardinal bucket = 0 then acc
      else
        let line =
          Printf.sprintf "%s -> %s" (Size.to_string size)
            (string_of_bucket bucket)
        in
        if acc = "" then line else acc ^ "\n" ^ line)
    tbl ""
