let sizeof_varinfo _ = 1
let sizeof_fieldinfo _ = 1
let sizeof_constant _ = 1

let rec sizeof_exp : type mode. mode Syntax.exp -> Size.t = function
  | Syntax.ExpHole _ -> 1
  | Syntax.Const constant -> 1 + sizeof_constant constant
  | Syntax.Lval lval -> 1 + sizeof_lval lval
  | Syntax.UnOp (_, exp, _) -> 1 + sizeof_exp exp
  | Syntax.BinOp (_, left, right, _) ->
      1 + sizeof_exp left + sizeof_exp right
  | Syntax.AddrOf lval | Syntax.StartOf lval -> 1 + sizeof_lval lval

and sizeof_lval : type mode. mode Syntax.lval -> Size.t =
 fun (host, offset) -> sizeof_lhost host + sizeof_offset offset

and sizeof_lhost : type mode. mode Syntax.lhost -> Size.t = function
  | Syntax.Var var -> 1 + sizeof_varinfo var
  | Syntax.Mem exp -> 1 + sizeof_exp exp

and sizeof_offset : type mode. mode Syntax.offset -> Size.t = function
  | Syntax.NoOffset -> 1
  | Syntax.Field (field, offset) ->
      1 + sizeof_fieldinfo field + sizeof_offset offset
  | Syntax.Index (exp, offset) ->
      1 + sizeof_exp exp + sizeof_offset offset

let sizeof_instr (type mode) (instr : mode Syntax.instr) =
  match instr with
  | Syntax.Set (lval, exp) -> 1 + sizeof_lval lval + sizeof_exp exp
  | Syntax.Call (return, callee, arguments) ->
      1
      + Option.fold ~none:0 ~some:sizeof_lval return
      + sizeof_exp callee
      + List.fold_left
          (fun size argument -> size + sizeof_exp argument)
          0 arguments

let rec sizeof_stmt : type mode. mode Syntax.stmt -> Size.t =
 fun stmt ->
  match stmt.Syntax.skind with
  | Syntax.Instr instrs ->
      1
      + List.fold_left
          (fun size instr -> size + sizeof_instr instr)
          0 instrs
  | Syntax.Return None -> 1
  | Syntax.Return (Some exp) -> 1 + sizeof_exp exp
  | Syntax.If (condition, then_block, else_block) ->
      1 + sizeof_exp condition + sizeof_block then_block
      + sizeof_block else_block
  | Syntax.Loop body -> 1 + sizeof_block body
  | Syntax.Break | Syntax.Continue -> 1
  | Syntax.Block block -> 1 + sizeof_block block

and sizeof_block : type mode. mode Syntax.block -> Size.t =
 fun block -> 1 + sizeof_stmt_seq_items block.Syntax.bstmts

and sizeof_stmt_seq_items :
    type mode. mode Syntax.stmt_seq_item list -> Size.t = function
  | [] -> 0
  | Syntax.Stmt stmt :: rest ->
      sizeof_stmt stmt + sizeof_stmt_seq_items rest
  | Syntax.StmtSeqHole _ :: rest ->
      1 + sizeof_stmt_seq_items rest

let sizeof_fundec (type mode) (fundec : mode Syntax.fundec) =
  1 + sizeof_varinfo fundec.Syntax.svar
  + List.fold_left
      (fun size formal -> size + sizeof_varinfo formal)
      0 fundec.Syntax.sformals
  + List.fold_left
      (fun size local -> size + sizeof_varinfo local)
      0 fundec.Syntax.slocals
  + sizeof_block fundec.Syntax.sbody

let rec sizeof_initinfo : type mode. mode Syntax.initinfo -> Size.t =
 fun initinfo ->
  match initinfo.Syntax.init with
  | None -> 0
  | Some init -> sizeof_init init

and sizeof_init : type mode. mode Syntax.init -> Size.t = function
  | Syntax.SingleInit exp -> 1 + sizeof_exp exp
  | Syntax.CompoundInit (_, fields) ->
      1
      + List.fold_left
          (fun size (offset, init) ->
            size + sizeof_offset offset + sizeof_init init)
          0 fields

let sizeof_global (type mode) (global : mode Syntax.global) =
  match global with
  | Syntax.GFun fundec -> sizeof_fundec fundec
  | Syntax.GVarDecl var -> 1 + sizeof_varinfo var
  | Syntax.GVar (var, initinfo) ->
      1 + sizeof_varinfo var + sizeof_initinfo initinfo

let sizeof_file (type mode) (file : mode Syntax.file) =
  1
  + List.fold_left
      (fun size global -> size + sizeof_global global)
      0 file.Syntax.globals
