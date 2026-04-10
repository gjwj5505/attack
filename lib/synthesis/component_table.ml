open Language

module ExpSet = Set.Make (struct
  type t = Syntax.Exp.t

  let compare = Stdlib.compare
end)

module CmdSet = Set.Make (struct
  type t = Syntax.Cmd.t

  let compare = Stdlib.compare
end)

module ETreeSet = Set.Make (struct
  type t = BigStep.etree

  let compare = Stdlib.compare
end)

module CTreeSet = Set.Make (struct
  type t = BigStep.ctree

  let compare = Stdlib.compare
end)

type bucket = {
  exps : ExpSet.t;
  cmds : CmdSet.t;
  etrees : ETreeSet.t;
  ctrees : CTreeSet.t;
}

type t = bucket Size_pair.Map.t

let empty_bucket =
  {
    exps = ExpSet.empty;
    cmds = CmdSet.empty;
    etrees = ETreeSet.empty;
    ctrees = CTreeSet.empty;
  }

let empty = Size_pair.Map.empty

let get_bucket size tbl =
  match Size_pair.Map.find_opt size tbl with
  | Some b -> b
  | None -> empty_bucket

let update_bucket size f tbl =
  let bucket = get_bucket size tbl in
  Size_pair.Map.add size (f bucket) tbl

let add_exp size e tbl =
  update_bucket size (fun b -> { b with exps = ExpSet.add e b.exps }) tbl

let add_cmd size c tbl =
  update_bucket size (fun b -> { b with cmds = CmdSet.add c b.cmds }) tbl

let add_etree size et tbl =
  update_bucket size (fun b -> { b with etrees = ETreeSet.add et b.etrees }) tbl

let add_ctree size ct tbl =
  update_bucket size (fun b -> { b with ctrees = CTreeSet.add ct b.ctrees }) tbl

let add_exp_exact e tbl =
  let size = Size_pair.make (Size.sizeof_Exp e) 0 in
  add_exp size e tbl

let add_cmd_exact c tbl =
  let size = Size_pair.make (Size.sizeof_Cmd c) 0 in
  add_cmd size c tbl

let add_etree_exact et tbl =
  let size = Size.sizeof_etree et in
  let size = Size_pair.make size.prog_size size.proof_size in
  add_etree size et tbl

let add_ctree_exact ct tbl =
  let size = Size.sizeof_ctree ct in
  let size = Size_pair.make size.prog_size size.proof_size in
  add_ctree size ct tbl

let exps_of_size size tbl = (get_bucket size tbl).exps
let cmds_of_size size tbl = (get_bucket size tbl).cmds
let etrees_of_size size tbl = (get_bucket size tbl).etrees
let ctrees_of_size size tbl = (get_bucket size tbl).ctrees

let fold_sizes f tbl init = Size_pair.Map.fold f tbl init

let bucket_cardinal b =
  ExpSet.cardinal b.exps + CmdSet.cardinal b.cmds + ETreeSet.cardinal b.etrees
  + CTreeSet.cardinal b.ctrees

let string_of_bucket b =
  Printf.sprintf "{exp=%d; cmd=%d; etree=%d; ctree=%d}"
    (ExpSet.cardinal b.exps) (CmdSet.cardinal b.cmds) (ETreeSet.cardinal b.etrees)
    (CTreeSet.cardinal b.ctrees)

let string_of_table tbl =
  fold_sizes
    (fun size bucket acc ->
      if bucket_cardinal bucket = 0 then acc
      else
        let line =
          Printf.sprintf "%s -> %s" (Size_pair.to_string size)
            (string_of_bucket bucket)
        in
        if acc = "" then line else acc ^ "\n" ^ line)
    tbl ""
