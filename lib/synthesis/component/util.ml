let empty_bucket : component_bucket =
  { exps   = ExpSet.empty
  ; cmds   = CmdSet.empty
  ; etrees = ETreeSet.empty
  ; ctrees = CTreeSet.empty
  }

let is_empty_bucket (b : component_bucket) : bool =
  ExpSet.is_empty b.exps
  && CmdSet.is_empty b.cmds
  && ETreeSet.is_empty b.etrees
  && CTreeSet.is_empty b.ctrees

let union_bucket (b1 : component_bucket) (b2 : component_bucket) : component_bucket =
  { exps   = ExpSet.union b1.exps b2.exps
  ; cmds   = CmdSet.union b1.cmds b2.cmds
  ; etrees = ETreeSet.union b1.etrees b2.etrees
  ; ctrees = CTreeSet.union b1.ctrees b2.ctrees
  }

let inter_bucket (b1 : component_bucket) (b2 : component_bucket) : component_bucket =
  { exps   = ExpSet.inter b1.exps b2.exps
  ; cmds   = CmdSet.inter b1.cmds b2.cmds
  ; etrees = ETreeSet.inter b1.etrees b2.etrees
  ; ctrees = CTreeSet.inter b1.ctrees b2.ctrees
  }

let diff_bucket (b1 : component_bucket) (b2 : component_bucket) : component_bucket =
  { exps   = ExpSet.diff b1.exps b2.exps
  ; cmds   = CmdSet.diff b1.cmds b2.cmds
  ; etrees = ETreeSet.diff b1.etrees b2.etrees
  ; ctrees = CTreeSet.diff b1.ctrees b2.ctrees
  }

let bucket_cardinal (b : component_bucket) : int =
  ExpSet.cardinal b.exps
  + CmdSet.cardinal b.cmds
  + ETreeSet.cardinal b.etrees
  + CTreeSet.cardinal b.ctrees

let bucket_cardinal_exps   (b : component_bucket) = ExpSet.cardinal b.exps
let bucket_cardinal_cmds   (b : component_bucket) = CmdSet.cardinal b.cmds
let bucket_cardinal_etrees (b : component_bucket) = ETreeSet.cardinal b.etrees
let bucket_cardinal_ctrees (b : component_bucket) = CTreeSet.cardinal b.ctrees

let bucket_cardinal_by_kind (b : component_bucket) : int * int * int * int =
  ( ExpSet.cardinal b.exps
  , CmdSet.cardinal b.cmds
  , ETreeSet.cardinal b.etrees
  , CTreeSet.cardinal b.ctrees
  )

let add_exp (e : Exp.t) (b : component_bucket) : component_bucket =
  { b with exps = ExpSet.add e b.exps }

let add_cmd (c : Cmd.t) (b : component_bucket) : component_bucket =
  { b with cmds = CmdSet.add c b.cmds }

let add_etree (et : etree) (b : component_bucket) : component_bucket =
  { b with etrees = ETreeSet.add et b.etrees }

let add_ctree (ct : ctree) (b : component_bucket) : component_bucket =
  { b with ctrees = CTreeSet.add ct b.ctrees }

let remove_exp (e : Exp.t) (b : component_bucket) : component_bucket =
  { b with exps = ExpSet.remove e b.exps }

let remove_cmd (c : Cmd.t) (b : component_bucket) : component_bucket =
  { b with cmds = CmdSet.remove c b.cmds }

let remove_etree (et : etree) (b : component_bucket) : component_bucket =
  { b with etrees = ETreeSet.remove et b.etrees }

let remove_ctree (ct : ctree) (b : component_bucket) : component_bucket =
  { b with ctrees = CTreeSet.remove ct b.ctrees }

let mem_exp (e : Exp.t) (b : component_bucket) : bool =
  ExpSet.mem e b.exps

let mem_cmd (c : Cmd.t) (b : component_bucket) : bool =
  CmdSet.mem c b.cmds

let mem_etree (et : etree) (b : component_bucket) : bool =
  ETreeSet.mem et b.etrees

let mem_ctree (ct : ctree) (b : component_bucket) : bool =
  CTreeSet.mem ct b.ctrees

let iter_bucket
    ~(fexp : Exp.t -> unit)
    ~(fcmd : Cmd.t -> unit)
    ~(fetree : etree -> unit)
    ~(fctree : ctree -> unit)
    (b : component_bucket)
  : unit =
  ExpSet.iter fexp b.exps;
  CmdSet.iter fcmd b.cmds;
  ETreeSet.iter fetree b.etrees;
  CTreeSet.iter fctree b.ctrees

let fold_bucket
    ~(fexp : Exp.t -> 'a -> 'a)
    ~(fcmd : Cmd.t -> 'a -> 'a)
    ~(fetree : etree -> 'a -> 'a)
    ~(fctree : ctree -> 'a -> 'a)
    (b : component_bucket)
    (init : 'a)
  : 'a =
  let acc = ExpSet.fold fexp b.exps init in
  let acc = CmdSet.fold fcmd b.cmds acc in
  let acc = ETreeSet.fold fetree b.etrees acc in
  let acc = CTreeSet.fold fctree b.ctrees acc in
  acc

let filter_bucket
    ~(pexp : Exp.t -> bool)
    ~(pcmd : Cmd.t -> bool)
    ~(petree : etree -> bool)
    ~(pctree : ctree -> bool)
    (b : component_bucket)
  : component_bucket =
  { exps   = ExpSet.filter pexp b.exps
  ; cmds   = CmdSet.filter pcmd b.cmds
  ; etrees = ETreeSet.filter petree b.etrees
  ; ctrees = CTreeSet.filter pctree b.ctrees
  }

let make_component_table (max_size : int) : component_table =
  if max_size < 0 then invalid_arg "make_component_table: negative max_size";
  Array.make (max_size + 1) empty_bucket

let table_max_size (tbl : component_table) : int =
  Array.length tbl - 1

let check_size_index (tbl : component_table) (n : int) : unit =
  if n < 0 || n >= Array.length tbl then
    invalid_arg "component_table: size index out of bounds"

let get_bucket (tbl : component_table) (n : int) : component_bucket =
  check_size_index tbl n;
  tbl.(n)

let set_bucket (tbl : component_table) (n : int) (b : component_bucket) : unit =
  check_size_index tbl n;
  tbl.(n) <- b

let update_bucket
    (tbl : component_table)
    (n : int)
    (f : component_bucket -> component_bucket)
  : unit =
  check_size_index tbl n;
  tbl.(n) <- f tbl.(n)

let exps_of_size (tbl : component_table) (n : int) : ExpSet.t =
  (get_bucket tbl n).exps

let cmds_of_size (tbl : component_table) (n : int) : CmdSet.t =
  (get_bucket tbl n).cmds

let etrees_of_size (tbl : component_table) (n : int) : ETreeSet.t =
  (get_bucket tbl n).etrees

let ctrees_of_size (tbl : component_table) (n : int) : CTreeSet.t =
  (get_bucket tbl n).ctrees

let add_exp_exact (tbl : component_table) (e : Exp.t) : unit =
  let n = Size.sizeof_Exp e in
  update_bucket tbl n (add_exp e)

let add_cmd_exact (tbl : component_table) (c : Cmd.t) : unit =
  let n = Size.sizeof_Cmd c in
  update_bucket tbl n (add_cmd c)

let add_etree_exact (tbl : component_table) (et : etree) : unit =
  let n = Size.sizeof_etree et in
  update_bucket tbl n (add_etree et)

let add_ctree_exact (tbl : component_table) (ct : ctree) : unit =
  let n = Size.sizeof_ctree ct in
  update_bucket tbl n (add_ctree ct)

let mem_exp_in_table (tbl : component_table) (e : Exp.t) : bool =
  let n = Size.sizeof_Exp e in
  n >= 0 && n < Array.length tbl && mem_exp e tbl.(n)

let mem_cmd_in_table (tbl : component_table) (c : Cmd.t) : bool =
  let n = Size.sizeof_Cmd c in
  n >= 0 && n < Array.length tbl && mem_cmd c tbl.(n)

let mem_etree_in_table (tbl : component_table) (et : etree) : bool =
  let n = Size.sizeof_etree et in
  n >= 0 && n < Array.length tbl && mem_etree et tbl.(n)

let mem_ctree_in_table (tbl : component_table) (ct : ctree) : bool =
  let n = Size.sizeof_ctree ct in
  n >= 0 && n < Array.length tbl && mem_ctree ct tbl.(n)

let bucket_is_exact_for_size (n : int) (b : component_bucket) : bool =
  ExpSet.for_all   (fun e  -> Size.sizeof_Exp e  = n) b.exps
  && CmdSet.for_all   (fun c  -> Size.sizeof_Cmd c  = n) b.cmds
  && ETreeSet.for_all (fun et -> Size.sizeof_etree et = n) b.etrees
  && CTreeSet.for_all (fun ct -> Size.sizeof_ctree ct = n) b.ctrees

let table_is_exact (tbl : component_table) : bool =
  let ok = ref true in
  for n = 0 to Array.length tbl - 1 do
    if not (bucket_is_exact_for_size n tbl.(n)) then ok := false
  done;
  !ok

  