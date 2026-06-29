module S = Syntax

let equal_list equal xs ys =
  List.length xs = List.length ys && List.for_all2 equal xs ys

let equal_option equal x y =
  match (x, y) with
  | None, None -> true
  | Some x, Some y -> equal x y
  | None, Some _ | Some _, None -> false

let equal_typ = ( = )

let equal_varinfo x y =
  String.equal x.S.vname y.S.vname
  && equal_typ x.S.vtype y.S.vtype
  && Bool.equal x.S.vglob y.S.vglob
  && Bool.equal x.S.vtemp y.S.vtemp
  && Int.equal x.S.vid y.S.vid

let equal_fieldinfo x y =
  String.equal x.S.fname y.S.fname && equal_typ x.S.ftype y.S.ftype

let equal_constant x y =
  match (x, y) with
  | S.Exp.CInt (nx, kx), S.Exp.CInt (ny, ky) ->
      Int64.equal nx ny && equal_typ kx ky

let equal_unop = ( = )
let equal_binop = ( = )

let rec equal_exp_t x y =
  match (x, y) with
  | S.Exp.Const x, S.Exp.Const y -> equal_constant x y
  | S.Exp.Lval x, S.Exp.Lval y -> equal_lval x y
  | S.Exp.UnOp (op_x, e_x, typ_x), S.Exp.UnOp (op_y, e_y, typ_y) ->
      equal_unop op_x op_y && equal_exp_t e_x e_y && equal_typ typ_x typ_y
  | ( S.Exp.BinOp (op_x, left_x, right_x, typ_x),
      S.Exp.BinOp (op_y, left_y, right_y, typ_y) ) ->
      equal_binop op_x op_y
      && equal_exp_t left_x left_y
      && equal_exp_t right_x right_y
      && equal_typ typ_x typ_y
  | S.Exp.AddrOf x, S.Exp.AddrOf y -> equal_lval x y
  | S.Exp.StartOf x, S.Exp.StartOf y -> equal_lval x y
  | (Const _ | Lval _ | UnOp _ | BinOp _ | AddrOf _ | StartOf _), _ ->
      false

and equal_lval (host_x, offset_x) (host_y, offset_y) =
  equal_lhost host_x host_y && equal_offset offset_x offset_y

and equal_lhost x y =
  match (x, y) with
  | S.Var x, S.Var y -> equal_varinfo x y
  | S.Mem x, S.Mem y -> equal_exp_t x y
  | (Var _ | Mem _), _ -> false

and equal_offset x y =
  match (x, y) with
  | S.NoOffset, S.NoOffset -> true
  | S.Field (field_x, offset_x), S.Field (field_y, offset_y) ->
      equal_fieldinfo field_x field_y && equal_offset offset_x offset_y
  | S.Index (e_x, offset_x), S.Index (e_y, offset_y) ->
      equal_exp_t e_x e_y && equal_offset offset_x offset_y
  | (NoOffset | Field _ | Index _), _ -> false

module Exp = struct
  let equal_constant = equal_constant
  let equal_unop = equal_unop
  let equal_binop = equal_binop
  let equal_t = equal_exp_t
end

let equal_instr x y =
  match (x, y) with
  | S.Set (lv_x, e_x), S.Set (lv_y, e_y) ->
      equal_lval lv_x lv_y && Exp.equal_t e_x e_y
  | S.Call (ret_x, f_x, args_x), S.Call (ret_y, f_y, args_y) ->
      equal_option equal_lval ret_x ret_y
      && Exp.equal_t f_x f_y
      && equal_list Exp.equal_t args_x args_y
  | (Set _ | Call _), _ -> false

let equal_label x y =
  match (x, y) with
  | S.Label x, S.Label y -> String.equal x y

let rec equal_block x y = equal_list equal_stmt x.S.bstmts y.S.bstmts

and equal_stmt x y =
  equal_list equal_label x.S.labels y.S.labels
  && equal_stmtkind x.S.skind y.S.skind

and equal_stmtkind x y =
  match (x, y) with
  | S.Instr x, S.Instr y -> equal_list equal_instr x y
  | S.Return x, S.Return y -> equal_option Exp.equal_t x y
  | S.If (cond_x, then_x, else_x), S.If (cond_y, then_y, else_y) ->
      Exp.equal_t cond_x cond_y
      && equal_block then_x then_y
      && equal_block else_x else_y
  | S.Loop x, S.Loop y -> equal_block x y
  | S.Break, S.Break -> true
  | S.Continue, S.Continue -> true
  | S.Block x, S.Block y -> equal_block x y
  | (Instr _ | Return _ | If _ | Loop _ | Break | Continue | Block _), _ ->
      false

let equal_fundec x y =
  equal_varinfo x.S.svar y.S.svar
  && equal_list equal_varinfo x.S.sformals y.S.sformals
  && equal_list equal_varinfo x.S.slocals y.S.slocals
  && equal_block x.S.sbody y.S.sbody

let rec equal_init x y =
  match (x, y) with
  | S.SingleInit x, S.SingleInit y -> Exp.equal_t x y
  | S.CompoundInit (typ_x, fields_x), S.CompoundInit (typ_y, fields_y) ->
      equal_typ typ_x typ_y
      && equal_list
           (fun (offset_x, init_x) (offset_y, init_y) ->
             equal_offset offset_x offset_y && equal_init init_x init_y)
           fields_x fields_y
  | (SingleInit _ | CompoundInit _), _ -> false

let equal_initinfo x y = equal_option equal_init x.S.init y.S.init

let equal_global x y =
  match (x, y) with
  | S.GFun x, S.GFun y -> equal_fundec x y
  | S.GVarDecl x, S.GVarDecl y -> equal_varinfo x y
  | S.GVar (vx, ix), S.GVar (vy, iy) ->
      equal_varinfo vx vy && equal_initinfo ix iy
  | (GFun _ | GVarDecl _ | GVar _), _ -> false

let equal_file x y =
  String.equal x.S.fileName y.S.fileName
  && equal_list equal_global x.S.globals y.S.globals
