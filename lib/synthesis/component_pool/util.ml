open Language
open Component_set

type component_bucket = bucket
type component_table = t

let empty_bucket = Component_set.empty_bucket
let empty_table = Component_set.empty

let is_empty_bucket bucket = Component_set.bucket_cardinal bucket = 0

let union_bucket b1 b2 =
  {
    exps = ExpSet.union b1.exps b2.exps;
    lvals = LvalSet.union b1.lvals b2.lvals;
    offsets = OffsetSet.union b1.offsets b2.offsets;
    instrs = InstrSet.union b1.instrs b2.instrs;
    stmts = StmtSet.union b1.stmts b2.stmts;
    blocks = BlockSet.union b1.blocks b2.blocks;
    fundecs = FundecSet.union b1.fundecs b2.fundecs;
    inits = InitSet.union b1.inits b2.inits;
    globals = GlobalSet.union b1.globals b2.globals;
    files = FileSet.union b1.files b2.files;
    etrees = ETreeSet.union b1.etrees b2.etrees;
    ltrees = LTreeSet.union b1.ltrees b2.ltrees;
    itrees = ITreeSet.union b1.itrees b2.itrees;
    strees = STreeSet.union b1.strees b2.strees;
    btrees = BTreeSet.union b1.btrees b2.btrees;
    ftrees = FTreeSet.union b1.ftrees b2.ftrees;
    ptrees = PTreeSet.union b1.ptrees b2.ptrees;
  }

let inter_bucket b1 b2 =
  {
    exps = ExpSet.inter b1.exps b2.exps;
    lvals = LvalSet.inter b1.lvals b2.lvals;
    offsets = OffsetSet.inter b1.offsets b2.offsets;
    instrs = InstrSet.inter b1.instrs b2.instrs;
    stmts = StmtSet.inter b1.stmts b2.stmts;
    blocks = BlockSet.inter b1.blocks b2.blocks;
    fundecs = FundecSet.inter b1.fundecs b2.fundecs;
    inits = InitSet.inter b1.inits b2.inits;
    globals = GlobalSet.inter b1.globals b2.globals;
    files = FileSet.inter b1.files b2.files;
    etrees = ETreeSet.inter b1.etrees b2.etrees;
    ltrees = LTreeSet.inter b1.ltrees b2.ltrees;
    itrees = ITreeSet.inter b1.itrees b2.itrees;
    strees = STreeSet.inter b1.strees b2.strees;
    btrees = BTreeSet.inter b1.btrees b2.btrees;
    ftrees = FTreeSet.inter b1.ftrees b2.ftrees;
    ptrees = PTreeSet.inter b1.ptrees b2.ptrees;
  }

let diff_bucket b1 b2 =
  {
    exps = ExpSet.diff b1.exps b2.exps;
    lvals = LvalSet.diff b1.lvals b2.lvals;
    offsets = OffsetSet.diff b1.offsets b2.offsets;
    instrs = InstrSet.diff b1.instrs b2.instrs;
    stmts = StmtSet.diff b1.stmts b2.stmts;
    blocks = BlockSet.diff b1.blocks b2.blocks;
    fundecs = FundecSet.diff b1.fundecs b2.fundecs;
    inits = InitSet.diff b1.inits b2.inits;
    globals = GlobalSet.diff b1.globals b2.globals;
    files = FileSet.diff b1.files b2.files;
    etrees = ETreeSet.diff b1.etrees b2.etrees;
    ltrees = LTreeSet.diff b1.ltrees b2.ltrees;
    itrees = ITreeSet.diff b1.itrees b2.itrees;
    strees = STreeSet.diff b1.strees b2.strees;
    btrees = BTreeSet.diff b1.btrees b2.btrees;
    ftrees = FTreeSet.diff b1.ftrees b2.ftrees;
    ptrees = PTreeSet.diff b1.ptrees b2.ptrees;
  }

let bucket_cardinal = Component_set.bucket_cardinal
let bucket_cardinal_exps b = ExpSet.cardinal b.exps
let bucket_cardinal_lvals b = LvalSet.cardinal b.lvals
let bucket_cardinal_offsets b = OffsetSet.cardinal b.offsets
let bucket_cardinal_instrs b = InstrSet.cardinal b.instrs
let bucket_cardinal_stmts b = StmtSet.cardinal b.stmts
let bucket_cardinal_blocks b = BlockSet.cardinal b.blocks
let bucket_cardinal_fundecs b = FundecSet.cardinal b.fundecs
let bucket_cardinal_inits b = InitSet.cardinal b.inits
let bucket_cardinal_globals b = GlobalSet.cardinal b.globals
let bucket_cardinal_files b = FileSet.cardinal b.files
let bucket_cardinal_etrees b = ETreeSet.cardinal b.etrees
let bucket_cardinal_ltrees b = LTreeSet.cardinal b.ltrees
let bucket_cardinal_itrees b = ITreeSet.cardinal b.itrees
let bucket_cardinal_strees b = STreeSet.cardinal b.strees
let bucket_cardinal_btrees b = BTreeSet.cardinal b.btrees
let bucket_cardinal_ftrees b = FTreeSet.cardinal b.ftrees
let bucket_cardinal_ptrees b = PTreeSet.cardinal b.ptrees

let add_exp exp b = { b with exps = ExpSet.add exp b.exps }
let add_lval lval b = { b with lvals = LvalSet.add lval b.lvals }
let add_offset offset b = { b with offsets = OffsetSet.add offset b.offsets }
let add_instr instr b = { b with instrs = InstrSet.add instr b.instrs }
let add_stmt stmt b = { b with stmts = StmtSet.add stmt b.stmts }
let add_block block b = { b with blocks = BlockSet.add block b.blocks }
let add_fundec fundec b = { b with fundecs = FundecSet.add fundec b.fundecs }
let add_init init b = { b with inits = InitSet.add init b.inits }
let add_global global b = { b with globals = GlobalSet.add global b.globals }
let add_file file b = { b with files = FileSet.add file b.files }
let add_etree etree b = { b with etrees = ETreeSet.add etree b.etrees }
let add_ltree ltree b = { b with ltrees = LTreeSet.add ltree b.ltrees }
let add_itree itree b = { b with itrees = ITreeSet.add itree b.itrees }
let add_stree stree b = { b with strees = STreeSet.add stree b.strees }
let add_btree btree b = { b with btrees = BTreeSet.add btree b.btrees }
let add_ftree ftree b = { b with ftrees = FTreeSet.add ftree b.ftrees }
let add_ptree ptree b = { b with ptrees = PTreeSet.add ptree b.ptrees }

let remove_exp exp b = { b with exps = ExpSet.remove exp b.exps }
let remove_lval lval b = { b with lvals = LvalSet.remove lval b.lvals }
let remove_offset offset b =
  { b with offsets = OffsetSet.remove offset b.offsets }
let remove_instr instr b = { b with instrs = InstrSet.remove instr b.instrs }
let remove_stmt stmt b = { b with stmts = StmtSet.remove stmt b.stmts }
let remove_block block b = { b with blocks = BlockSet.remove block b.blocks }
let remove_fundec fundec b =
  { b with fundecs = FundecSet.remove fundec b.fundecs }
let remove_init init b = { b with inits = InitSet.remove init b.inits }
let remove_global global b =
  { b with globals = GlobalSet.remove global b.globals }
let remove_file file b = { b with files = FileSet.remove file b.files }
let remove_etree etree b = { b with etrees = ETreeSet.remove etree b.etrees }
let remove_ltree ltree b = { b with ltrees = LTreeSet.remove ltree b.ltrees }
let remove_itree itree b = { b with itrees = ITreeSet.remove itree b.itrees }
let remove_stree stree b = { b with strees = STreeSet.remove stree b.strees }
let remove_btree btree b = { b with btrees = BTreeSet.remove btree b.btrees }
let remove_ftree ftree b = { b with ftrees = FTreeSet.remove ftree b.ftrees }
let remove_ptree ptree b = { b with ptrees = PTreeSet.remove ptree b.ptrees }

let mem_exp exp b = ExpSet.mem exp b.exps
let mem_lval lval b = LvalSet.mem lval b.lvals
let mem_offset offset b = OffsetSet.mem offset b.offsets
let mem_instr instr b = InstrSet.mem instr b.instrs
let mem_stmt stmt b = StmtSet.mem stmt b.stmts
let mem_block block b = BlockSet.mem block b.blocks
let mem_fundec fundec b = FundecSet.mem fundec b.fundecs
let mem_init init b = InitSet.mem init b.inits
let mem_global global b = GlobalSet.mem global b.globals
let mem_file file b = FileSet.mem file b.files
let mem_etree etree b = ETreeSet.mem etree b.etrees
let mem_ltree ltree b = LTreeSet.mem ltree b.ltrees
let mem_itree itree b = ITreeSet.mem itree b.itrees
let mem_stree stree b = STreeSet.mem stree b.strees
let mem_btree btree b = BTreeSet.mem btree b.btrees
let mem_ftree ftree b = FTreeSet.mem ftree b.ftrees
let mem_ptree ptree b = PTreeSet.mem ptree b.ptrees

let get_bucket = Component_set.get_bucket
let update_bucket = Component_set.update_bucket
let fold_sizes = Component_set.fold_sizes

let add_exp_exact = Component_set.add_exp_exact
let add_lval_exact = Component_set.add_lval_exact
let add_offset_exact = Component_set.add_offset_exact
let add_instr_exact = Component_set.add_instr_exact
let add_stmt_exact = Component_set.add_stmt_exact
let add_block_exact = Component_set.add_block_exact
let add_fundec_exact = Component_set.add_fundec_exact
let add_init_exact = Component_set.add_init_exact
let add_global_exact = Component_set.add_global_exact
let add_file_exact = Component_set.add_file_exact
let add_etree_exact = Component_set.add_etree_exact
let add_ltree_exact = Component_set.add_ltree_exact
let add_itree_exact = Component_set.add_itree_exact
let add_stree_exact = Component_set.add_stree_exact
let add_btree_exact = Component_set.add_btree_exact
let add_ftree_exact = Component_set.add_ftree_exact
let add_ptree_exact = Component_set.add_ptree_exact

let bucket_is_exact_for_size size b =
  ExpSet.for_all
    (fun exp -> Size.equal (Size.make (Size.sizeof_exp exp) 0) size)
    b.exps
  && LvalSet.for_all
       (fun lval -> Size.equal (Size.make (Size.sizeof_lval lval) 0) size)
       b.lvals
  && OffsetSet.for_all
       (fun offset -> Size.equal (Size.make (Size.sizeof_offset offset) 0) size)
       b.offsets
  && InstrSet.for_all
       (fun instr -> Size.equal (Size.make (Size.sizeof_instr instr) 0) size)
       b.instrs
  && StmtSet.for_all
       (fun stmt -> Size.equal (Size.make (Size.sizeof_stmt stmt) 0) size)
       b.stmts
  && BlockSet.for_all
       (fun block -> Size.equal (Size.make (Size.sizeof_block block) 0) size)
       b.blocks
  && FundecSet.for_all
       (fun fundec -> Size.equal (Size.make (Size.sizeof_fundec fundec) 0) size)
       b.fundecs
  && InitSet.for_all
       (fun init -> Size.equal (Size.make (Size.sizeof_init init) 0) size)
       b.inits
  && GlobalSet.for_all
       (fun global -> Size.equal (Size.make (Size.sizeof_global global) 0) size)
       b.globals
  && FileSet.for_all
       (fun file -> Size.equal (Size.make (Size.sizeof_file file) 0) size)
       b.files
  && ETreeSet.for_all
       (fun etree -> Size.equal (Size.sizeof_tree (BigStep.ETree etree)) size)
       b.etrees
  && LTreeSet.for_all
       (fun ltree -> Size.equal (Size.sizeof_tree (BigStep.LTree ltree)) size)
       b.ltrees
  && ITreeSet.for_all
       (fun itree -> Size.equal (Size.sizeof_tree (BigStep.ITree itree)) size)
       b.itrees
  && STreeSet.for_all
       (fun stree -> Size.equal (Size.sizeof_tree (BigStep.STree stree)) size)
       b.strees
  && BTreeSet.for_all
       (fun btree -> Size.equal (Size.sizeof_tree (BigStep.BTree btree)) size)
       b.btrees
  && FTreeSet.for_all
       (fun ftree -> Size.equal (Size.sizeof_tree (BigStep.FTree ftree)) size)
       b.ftrees
  && PTreeSet.for_all
       (fun ptree -> Size.equal (Size.sizeof_tree (BigStep.PTree ptree)) size)
       b.ptrees

let table_is_exact tbl =
  Size.Map.for_all bucket_is_exact_for_size tbl
