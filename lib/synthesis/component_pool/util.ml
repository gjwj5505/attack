open Language
open Component_set

type component_bucket = bucket
type component_table = t

let empty_bucket = Component_set.empty_bucket
let empty_table = Component_set.empty

let is_empty_bucket (b : component_bucket) : bool =
  ExpSet.is_empty b.exps && CmdSet.is_empty b.cmds && ETreeSet.is_empty b.etrees
  && CTreeSet.is_empty b.ctrees

let union_bucket (b1 : component_bucket) (b2 : component_bucket) :
    component_bucket =
  {
    exps = ExpSet.union b1.exps b2.exps;
    cmds = CmdSet.union b1.cmds b2.cmds;
    etrees = ETreeSet.union b1.etrees b2.etrees;
    ctrees = CTreeSet.union b1.ctrees b2.ctrees;
  }

let inter_bucket (b1 : component_bucket) (b2 : component_bucket) :
    component_bucket =
  {
    exps = ExpSet.inter b1.exps b2.exps;
    cmds = CmdSet.inter b1.cmds b2.cmds;
    etrees = ETreeSet.inter b1.etrees b2.etrees;
    ctrees = CTreeSet.inter b1.ctrees b2.ctrees;
  }

let diff_bucket (b1 : component_bucket) (b2 : component_bucket) :
    component_bucket =
  {
    exps = ExpSet.diff b1.exps b2.exps;
    cmds = CmdSet.diff b1.cmds b2.cmds;
    etrees = ETreeSet.diff b1.etrees b2.etrees;
    ctrees = CTreeSet.diff b1.ctrees b2.ctrees;
  }

let bucket_cardinal = Component_set.bucket_cardinal
let bucket_cardinal_exps (b : component_bucket) = ExpSet.cardinal b.exps
let bucket_cardinal_cmds (b : component_bucket) = CmdSet.cardinal b.cmds
let bucket_cardinal_etrees (b : component_bucket) = ETreeSet.cardinal b.etrees
let bucket_cardinal_ctrees (b : component_bucket) = CTreeSet.cardinal b.ctrees

let bucket_cardinal_by_kind (b : component_bucket) : int * int * int * int =
  ( ExpSet.cardinal b.exps,
    CmdSet.cardinal b.cmds,
    ETreeSet.cardinal b.etrees,
    CTreeSet.cardinal b.ctrees )

let add_exp (e : Syntax.Exp.t) (b : component_bucket) : component_bucket =
  { b with exps = ExpSet.add e b.exps }

let add_cmd (c : Syntax.Cmd.t) (b : component_bucket) : component_bucket =
  { b with cmds = CmdSet.add c b.cmds }

let add_etree (et : BigStep.etree) (b : component_bucket) : component_bucket =
  { b with etrees = ETreeSet.add et b.etrees }

let add_ctree (ct : BigStep.ctree) (b : component_bucket) : component_bucket =
  { b with ctrees = CTreeSet.add ct b.ctrees }

let remove_exp (e : Syntax.Exp.t) (b : component_bucket) : component_bucket =
  { b with exps = ExpSet.remove e b.exps }

let remove_cmd (c : Syntax.Cmd.t) (b : component_bucket) : component_bucket =
  { b with cmds = CmdSet.remove c b.cmds }

let remove_etree (et : BigStep.etree) (b : component_bucket) : component_bucket
    =
  { b with etrees = ETreeSet.remove et b.etrees }

let remove_ctree (ct : BigStep.ctree) (b : component_bucket) : component_bucket
    =
  { b with ctrees = CTreeSet.remove ct b.ctrees }

let mem_exp (e : Syntax.Exp.t) (b : component_bucket) : bool =
  ExpSet.mem e b.exps

let mem_cmd (c : Syntax.Cmd.t) (b : component_bucket) : bool =
  CmdSet.mem c b.cmds

let mem_etree (et : BigStep.etree) (b : component_bucket) : bool =
  ETreeSet.mem et b.etrees

let mem_ctree (ct : BigStep.ctree) (b : component_bucket) : bool =
  CTreeSet.mem ct b.ctrees

let iter_bucket ~(fexp : Syntax.Exp.t -> unit) ~(fcmd : Syntax.Cmd.t -> unit)
    ~(fetree : BigStep.etree -> unit) ~(fctree : BigStep.ctree -> unit)
    (b : component_bucket) : unit =
  ExpSet.iter fexp b.exps;
  CmdSet.iter fcmd b.cmds;
  ETreeSet.iter fetree b.etrees;
  CTreeSet.iter fctree b.ctrees

let fold_bucket ~(fexp : Syntax.Exp.t -> 'a -> 'a)
    ~(fcmd : Syntax.Cmd.t -> 'a -> 'a) ~(fetree : BigStep.etree -> 'a -> 'a)
    ~(fctree : BigStep.ctree -> 'a -> 'a) (b : component_bucket) (init : 'a) :
    'a =
  let acc = ExpSet.fold fexp b.exps init in
  let acc = CmdSet.fold fcmd b.cmds acc in
  let acc = ETreeSet.fold fetree b.etrees acc in
  CTreeSet.fold fctree b.ctrees acc

let filter_bucket ~(pexp : Syntax.Exp.t -> bool) ~(pcmd : Syntax.Cmd.t -> bool)
    ~(petree : BigStep.etree -> bool) ~(pctree : BigStep.ctree -> bool)
    (b : component_bucket) : component_bucket =
  {
    exps = ExpSet.filter pexp b.exps;
    cmds = CmdSet.filter pcmd b.cmds;
    etrees = ETreeSet.filter petree b.etrees;
    ctrees = CTreeSet.filter pctree b.ctrees;
  }

let get_bucket = Component_set.get_bucket
let update_bucket = Component_set.update_bucket
let exps_of_size = Component_set.exps_of_size
let cmds_of_size = Component_set.cmds_of_size
let etrees_of_size = Component_set.etrees_of_size
let ctrees_of_size = Component_set.ctrees_of_size
let add_exp_exact = Component_set.add_exp_exact
let add_cmd_exact = Component_set.add_cmd_exact
let add_etree_exact = Component_set.add_etree_exact
let add_ctree_exact = Component_set.add_ctree_exact

let mem_exp_in_table (tbl : component_table) (e : Syntax.Exp.t) : bool =
  mem_exp e (get_bucket (Size.make (Size.sizeof_Exp e) 0) tbl)

let mem_cmd_in_table (tbl : component_table) (c : Syntax.Cmd.t) : bool =
  mem_cmd c (get_bucket (Size.make (Size.sizeof_Cmd c) 0) tbl)

let mem_etree_in_table (tbl : component_table) (et : BigStep.etree) : bool =
  mem_etree et (get_bucket (Size.sizeof_etree et) tbl)

let mem_ctree_in_table (tbl : component_table) (ct : BigStep.ctree) : bool =
  mem_ctree ct (get_bucket (Size.sizeof_ctree ct) tbl)

let bucket_is_exact_for_size (size : Size.size) (b : component_bucket) : bool =
  ExpSet.for_all
    (fun e -> Size.equal (Size.make (Size.sizeof_Exp e) 0) size)
    b.exps
  && CmdSet.for_all
       (fun c -> Size.equal (Size.make (Size.sizeof_Cmd c) 0) size)
       b.cmds
  && ETreeSet.for_all
       (fun et -> Size.equal (Size.sizeof_etree et) size)
       b.etrees
  && CTreeSet.for_all
       (fun ct -> Size.equal (Size.sizeof_ctree ct) size)
       b.ctrees

let table_is_exact (tbl : component_table) : bool =
  Size.Map.for_all bucket_is_exact_for_size tbl
