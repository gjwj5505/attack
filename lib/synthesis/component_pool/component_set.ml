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
end

module ExpSet = Make_payload_set (Exp_component)
module LvalSet = Make_payload_set (Lval_component)
module OffsetSet = Make_payload_set (Offset_component)
module InstrSet = Make_payload_set (Instr_component)
module StmtSet = Make_payload_set (Stmt_component)
module BlockSet = Make_payload_set (Block_component)
module FundecSet = Make_payload_set (Fundec_component)
module InitSet = Make_payload_set (Init_component)
module GlobalSet = Make_payload_set (Global_component)
module FileSet = Make_payload_set (File_component)

module ETreeSet = Make_payload_set (ETree_component)
module LTreeSet = Make_payload_set (LTree_component)
module ITreeSet = Make_payload_set (ITree_component)
module STreeSet = Make_payload_set (STree_component)
module BTreeSet = Make_payload_set (BTree_component)
module FTreeSet = Make_payload_set (FTree_component)
module PTreeSet = Make_payload_set (PTree_component)

type bucket = {
  exps : ExpSet.t;
  lvals : LvalSet.t;
  offsets : OffsetSet.t;
  instrs : InstrSet.t;
  stmts : StmtSet.t;
  blocks : BlockSet.t;
  fundecs : FundecSet.t;
  inits : InitSet.t;
  globals : GlobalSet.t;
  files : FileSet.t;
  etrees : ETreeSet.t;
  ltrees : LTreeSet.t;
  itrees : ITreeSet.t;
  strees : STreeSet.t;
  btrees : BTreeSet.t;
  ftrees : FTreeSet.t;
  ptrees : PTreeSet.t;
}

type t = bucket Size.Map.t

let empty_bucket =
  {
    exps = ExpSet.empty;
    lvals = LvalSet.empty;
    offsets = OffsetSet.empty;
    instrs = InstrSet.empty;
    stmts = StmtSet.empty;
    blocks = BlockSet.empty;
    fundecs = FundecSet.empty;
    inits = InitSet.empty;
    globals = GlobalSet.empty;
    files = FileSet.empty;
    etrees = ETreeSet.empty;
    ltrees = LTreeSet.empty;
    itrees = ITreeSet.empty;
    strees = STreeSet.empty;
    btrees = BTreeSet.empty;
    ftrees = FTreeSet.empty;
    ptrees = PTreeSet.empty;
  }

let empty = Size.Map.empty

let get_bucket bucket_size tbl =
  match Size.Map.find_opt bucket_size tbl with
  | Some b -> b
  | None -> empty_bucket

let update_bucket bucket_size f tbl =
  let bucket = get_bucket bucket_size tbl in
  Size.Map.add bucket_size (f bucket) tbl

let add_exp size exp tbl =
  update_bucket size (fun b -> { b with exps = ExpSet.add exp b.exps }) tbl

let add_lval size lval tbl =
  update_bucket size (fun b -> { b with lvals = LvalSet.add lval b.lvals }) tbl

let add_offset size offset tbl =
  update_bucket size
    (fun b -> { b with offsets = OffsetSet.add offset b.offsets })
    tbl

let add_instr size instr tbl =
  update_bucket size
    (fun b -> { b with instrs = InstrSet.add instr b.instrs })
    tbl

let add_stmt size stmt tbl =
  update_bucket size (fun b -> { b with stmts = StmtSet.add stmt b.stmts }) tbl

let add_block size block tbl =
  update_bucket size
    (fun b -> { b with blocks = BlockSet.add block b.blocks })
    tbl

let add_fundec size fundec tbl =
  update_bucket size
    (fun b -> { b with fundecs = FundecSet.add fundec b.fundecs })
    tbl

let add_init size init tbl =
  update_bucket size (fun b -> { b with inits = InitSet.add init b.inits }) tbl

let add_global size global tbl =
  update_bucket size
    (fun b -> { b with globals = GlobalSet.add global b.globals })
    tbl

let add_file size file tbl =
  update_bucket size (fun b -> { b with files = FileSet.add file b.files }) tbl

let add_etree size etree tbl =
  update_bucket size
    (fun b -> { b with etrees = ETreeSet.add etree b.etrees })
    tbl

let add_ltree size ltree tbl =
  update_bucket size
    (fun b -> { b with ltrees = LTreeSet.add ltree b.ltrees })
    tbl

let add_itree size itree tbl =
  update_bucket size
    (fun b -> { b with itrees = ITreeSet.add itree b.itrees })
    tbl

let add_stree size stree tbl =
  update_bucket size
    (fun b -> { b with strees = STreeSet.add stree b.strees })
    tbl

let add_btree size btree tbl =
  update_bucket size
    (fun b -> { b with btrees = BTreeSet.add btree b.btrees })
    tbl

let add_ftree size ftree tbl =
  update_bucket size
    (fun b -> { b with ftrees = FTreeSet.add ftree b.ftrees })
    tbl

let add_ptree size ptree tbl =
  update_bucket size
    (fun b -> { b with ptrees = PTreeSet.add ptree b.ptrees })
    tbl

let syntax_size n = Size.make n 0

let add_exp_exact exp tbl = add_exp (syntax_size (Size.sizeof_exp exp)) exp tbl
let add_lval_exact lval tbl = add_lval (syntax_size (Size.sizeof_lval lval)) lval tbl
let add_offset_exact offset tbl =
  add_offset (syntax_size (Size.sizeof_offset offset)) offset tbl
let add_instr_exact instr tbl =
  add_instr (syntax_size (Size.sizeof_instr instr)) instr tbl
let add_stmt_exact stmt tbl = add_stmt (syntax_size (Size.sizeof_stmt stmt)) stmt tbl
let add_block_exact block tbl =
  add_block (syntax_size (Size.sizeof_block block)) block tbl
let add_fundec_exact fundec tbl =
  add_fundec (syntax_size (Size.sizeof_fundec fundec)) fundec tbl
let add_init_exact init tbl = add_init (syntax_size (Size.sizeof_init init)) init tbl
let add_global_exact global tbl =
  add_global (syntax_size (Size.sizeof_global global)) global tbl
let add_file_exact file tbl = add_file (syntax_size (Size.sizeof_file file)) file tbl

let add_etree_exact etree tbl = add_etree (Size.sizeof_tree (BigStep.ETree etree)) etree tbl
let add_ltree_exact ltree tbl = add_ltree (Size.sizeof_tree (BigStep.LTree ltree)) ltree tbl
let add_itree_exact itree tbl = add_itree (Size.sizeof_tree (BigStep.ITree itree)) itree tbl
let add_stree_exact stree tbl = add_stree (Size.sizeof_tree (BigStep.STree stree)) stree tbl
let add_btree_exact btree tbl = add_btree (Size.sizeof_tree (BigStep.BTree btree)) btree tbl
let add_ftree_exact ftree tbl = add_ftree (Size.sizeof_tree (BigStep.FTree ftree)) ftree tbl
let add_ptree_exact ptree tbl = add_ptree (Size.sizeof_tree (BigStep.PTree ptree)) ptree tbl

let exps_of_size size tbl = (get_bucket size tbl).exps
let lvals_of_size size tbl = (get_bucket size tbl).lvals
let offsets_of_size size tbl = (get_bucket size tbl).offsets
let instrs_of_size size tbl = (get_bucket size tbl).instrs
let stmts_of_size size tbl = (get_bucket size tbl).stmts
let blocks_of_size size tbl = (get_bucket size tbl).blocks
let fundecs_of_size size tbl = (get_bucket size tbl).fundecs
let inits_of_size size tbl = (get_bucket size tbl).inits
let globals_of_size size tbl = (get_bucket size tbl).globals
let files_of_size size tbl = (get_bucket size tbl).files

let etrees_of_size size tbl = (get_bucket size tbl).etrees
let ltrees_of_size size tbl = (get_bucket size tbl).ltrees
let itrees_of_size size tbl = (get_bucket size tbl).itrees
let strees_of_size size tbl = (get_bucket size tbl).strees
let btrees_of_size size tbl = (get_bucket size tbl).btrees
let ftrees_of_size size tbl = (get_bucket size tbl).ftrees
let ptrees_of_size size tbl = (get_bucket size tbl).ptrees

let fold_exps size tbl f acc = ExpSet.fold f (exps_of_size size tbl) acc
let fold_lvals size tbl f acc = LvalSet.fold f (lvals_of_size size tbl) acc
let fold_offsets size tbl f acc = OffsetSet.fold f (offsets_of_size size tbl) acc
let fold_instrs size tbl f acc = InstrSet.fold f (instrs_of_size size tbl) acc
let fold_stmts size tbl f acc = StmtSet.fold f (stmts_of_size size tbl) acc
let fold_blocks size tbl f acc = BlockSet.fold f (blocks_of_size size tbl) acc
let fold_fundecs size tbl f acc = FundecSet.fold f (fundecs_of_size size tbl) acc
let fold_inits size tbl f acc = InitSet.fold f (inits_of_size size tbl) acc
let fold_globals size tbl f acc = GlobalSet.fold f (globals_of_size size tbl) acc
let fold_files size tbl f acc = FileSet.fold f (files_of_size size tbl) acc

let fold_etrees size tbl f acc = ETreeSet.fold f (etrees_of_size size tbl) acc
let fold_ltrees size tbl f acc = LTreeSet.fold f (ltrees_of_size size tbl) acc
let fold_itrees size tbl f acc = ITreeSet.fold f (itrees_of_size size tbl) acc
let fold_strees size tbl f acc = STreeSet.fold f (strees_of_size size tbl) acc
let fold_btrees size tbl f acc = BTreeSet.fold f (btrees_of_size size tbl) acc
let fold_ftrees size tbl f acc = FTreeSet.fold f (ftrees_of_size size tbl) acc
let fold_ptrees size tbl f acc = PTreeSet.fold f (ptrees_of_size size tbl) acc

let exp_elements = ExpSet.elements
let lval_elements = LvalSet.elements
let offset_elements = OffsetSet.elements
let instr_elements = InstrSet.elements
let stmt_elements = StmtSet.elements
let block_elements = BlockSet.elements
let fundec_elements = FundecSet.elements
let init_elements = InitSet.elements
let global_elements = GlobalSet.elements
let file_elements = FileSet.elements

let etree_elements = ETreeSet.elements
let ltree_elements = LTreeSet.elements
let itree_elements = ITreeSet.elements
let stree_elements = STreeSet.elements
let btree_elements = BTreeSet.elements
let ftree_elements = FTreeSet.elements
let ptree_elements = PTreeSet.elements

let scored_exp_elements size tbl = ExpSet.scored_elements (exps_of_size size tbl)
let scored_lval_elements size tbl = LvalSet.scored_elements (lvals_of_size size tbl)
let scored_offset_elements size tbl =
  OffsetSet.scored_elements (offsets_of_size size tbl)
let scored_instr_elements size tbl =
  InstrSet.scored_elements (instrs_of_size size tbl)
let scored_stmt_elements size tbl = StmtSet.scored_elements (stmts_of_size size tbl)
let scored_block_elements size tbl =
  BlockSet.scored_elements (blocks_of_size size tbl)
let scored_fundec_elements size tbl =
  FundecSet.scored_elements (fundecs_of_size size tbl)
let scored_init_elements size tbl = InitSet.scored_elements (inits_of_size size tbl)
let scored_global_elements size tbl =
  GlobalSet.scored_elements (globals_of_size size tbl)
let scored_file_elements size tbl = FileSet.scored_elements (files_of_size size tbl)

let scored_etree_elements size tbl =
  ETreeSet.scored_elements (etrees_of_size size tbl)
let scored_ltree_elements size tbl =
  LTreeSet.scored_elements (ltrees_of_size size tbl)
let scored_itree_elements size tbl =
  ITreeSet.scored_elements (itrees_of_size size tbl)
let scored_stree_elements size tbl =
  STreeSet.scored_elements (strees_of_size size tbl)
let scored_btree_elements size tbl =
  BTreeSet.scored_elements (btrees_of_size size tbl)
let scored_ftree_elements size tbl =
  FTreeSet.scored_elements (ftrees_of_size size tbl)
let scored_ptree_elements size tbl =
  PTreeSet.scored_elements (ptrees_of_size size tbl)

let contains_exp = ExpSet.mem
let contains_lval = LvalSet.mem
let contains_offset = OffsetSet.mem
let contains_instr = InstrSet.mem
let contains_stmt = StmtSet.mem
let contains_block = BlockSet.mem
let contains_fundec = FundecSet.mem
let contains_init = InitSet.mem
let contains_global = GlobalSet.mem
let contains_file = FileSet.mem

let contains_etree = ETreeSet.mem
let contains_ltree = LTreeSet.mem
let contains_itree = ITreeSet.mem
let contains_stree = STreeSet.mem
let contains_btree = BTreeSet.mem
let contains_ftree = FTreeSet.mem
let contains_ptree = PTreeSet.mem

let fold_sizes f tbl init = Size.Map.fold f tbl init

let bucket_cardinal b =
  ExpSet.cardinal b.exps
  + LvalSet.cardinal b.lvals
  + OffsetSet.cardinal b.offsets
  + InstrSet.cardinal b.instrs
  + StmtSet.cardinal b.stmts
  + BlockSet.cardinal b.blocks
  + FundecSet.cardinal b.fundecs
  + InitSet.cardinal b.inits
  + GlobalSet.cardinal b.globals
  + FileSet.cardinal b.files
  + ETreeSet.cardinal b.etrees
  + LTreeSet.cardinal b.ltrees
  + ITreeSet.cardinal b.itrees
  + STreeSet.cardinal b.strees
  + BTreeSet.cardinal b.btrees
  + FTreeSet.cardinal b.ftrees
  + PTreeSet.cardinal b.ptrees

let string_of_bucket b =
  Printf.sprintf
    "{exp=%d; lval=%d; offset=%d; instr=%d; stmt=%d; block=%d; fundec=%d; init=%d; global=%d; file=%d; etree=%d; ltree=%d; itree=%d; stree=%d; btree=%d; ftree=%d; ptree=%d}"
    (ExpSet.cardinal b.exps) (LvalSet.cardinal b.lvals)
    (OffsetSet.cardinal b.offsets) (InstrSet.cardinal b.instrs)
    (StmtSet.cardinal b.stmts) (BlockSet.cardinal b.blocks)
    (FundecSet.cardinal b.fundecs) (InitSet.cardinal b.inits)
    (GlobalSet.cardinal b.globals) (FileSet.cardinal b.files)
    (ETreeSet.cardinal b.etrees) (LTreeSet.cardinal b.ltrees)
    (ITreeSet.cardinal b.itrees) (STreeSet.cardinal b.strees)
    (BTreeSet.cardinal b.btrees) (FTreeSet.cardinal b.ftrees)
    (PTreeSet.cardinal b.ptrees)

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
