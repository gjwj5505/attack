open Syntax

let equal_list equal xs ys =
  List.length xs = List.length ys && List.for_all2 equal xs ys

let equal_option equal x y =
  match (x, y) with
  | None, None -> true
  | Some x, Some y -> equal x y
  | None, Some _ | Some _, None -> false

let equal_typ = ( = )

let equal_varinfo x y =
  String.equal x.vname y.vname
  && equal_typ x.vtype y.vtype
  && Bool.equal x.vglob y.vglob
  && Bool.equal x.vtemp y.vtemp
  && Int.equal x.vid y.vid

let equal_fieldinfo x y =
  String.equal x.fname y.fname && equal_typ x.ftype y.ftype

let equal_constant x y =
  match (x, y) with
  | CInt (nx, kx), CInt (ny, ky) ->
      Int64.equal nx ny && equal_typ kx ky

let equal_unop = ( = )
let equal_binop = ( = )

let rec equal_exp_t x y =
  match (x, y) with
  | Const x, Const y -> equal_constant x y
  | Lval x, Lval y -> equal_lval x y
  | UnOp (op_x, e_x, typ_x), UnOp (op_y, e_y, typ_y) ->
      equal_unop op_x op_y && equal_exp_t e_x e_y && equal_typ typ_x typ_y
  | ( BinOp (op_x, left_x, right_x, typ_x),
      BinOp (op_y, left_y, right_y, typ_y) ) ->
      equal_binop op_x op_y
      && equal_exp_t left_x left_y
      && equal_exp_t right_x right_y
      && equal_typ typ_x typ_y
  | AddrOf x, AddrOf y -> equal_lval x y
  | StartOf x, StartOf y -> equal_lval x y
  | (Const _ | Lval _ | UnOp _ | BinOp _ | AddrOf _ | StartOf _), _ ->
      false

and equal_lval (host_x, offset_x) (host_y, offset_y) =
  equal_lhost host_x host_y && equal_offset offset_x offset_y

and equal_lhost x y =
  match (x, y) with
  | Var x, Var y -> equal_varinfo x y
  | Mem x, Mem y -> equal_exp_t x y
  | (Var _ | Mem _), _ -> false

and equal_offset x y =
  match (x, y) with
  | NoOffset, NoOffset -> true
  | Field (field_x, offset_x), Field (field_y, offset_y) ->
      equal_fieldinfo field_x field_y && equal_offset offset_x offset_y
  | Index (e_x, offset_x), Index (e_y, offset_y) ->
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
  | Set (lv_x, e_x), Set (lv_y, e_y) ->
      equal_lval lv_x lv_y && Exp.equal_t e_x e_y
  | Call (ret_x, f_x, args_x), Call (ret_y, f_y, args_y) ->
      equal_option equal_lval ret_x ret_y
      && Exp.equal_t f_x f_y
      && equal_list Exp.equal_t args_x args_y
  | (Set _ | Call _), _ -> false

let equal_label x y =
  match (x, y) with
  | Label x, Label y -> String.equal x y

let rec equal_block x y = equal_list equal_stmt x.bstmts y.bstmts

and equal_stmt x y =
  equal_list equal_label x.labels y.labels
  && equal_stmtkind x.skind y.skind

and equal_stmtkind x y =
  match (x, y) with
  | Instr x, Instr y -> equal_list equal_instr x y
  | Return x, Return y -> equal_option Exp.equal_t x y
  | If (cond_x, then_x, else_x), If (cond_y, then_y, else_y) ->
      Exp.equal_t cond_x cond_y
      && equal_block then_x then_y
      && equal_block else_x else_y
  | Loop x, Loop y -> equal_block x y
  | Break, Break -> true
  | Continue, Continue -> true
  | Block x, Block y -> equal_block x y
  | (Instr _ | Return _ | If _ | Loop _ | Break | Continue | Block _), _ ->
      false

let equal_fundec x y =
  equal_varinfo x.svar y.svar
  && equal_list equal_varinfo x.sformals y.sformals
  && equal_list equal_varinfo x.slocals y.slocals
  && equal_block x.sbody y.sbody

let rec equal_init x y =
  match (x, y) with
  | SingleInit x, SingleInit y -> Exp.equal_t x y
  | CompoundInit (typ_x, fields_x), CompoundInit (typ_y, fields_y) ->
      equal_typ typ_x typ_y
      && equal_list
           (fun (offset_x, init_x) (offset_y, init_y) ->
             equal_offset offset_x offset_y && equal_init init_x init_y)
           fields_x fields_y
  | (SingleInit _ | CompoundInit _), _ -> false

let equal_initinfo x y = equal_option equal_init x.init y.init

let equal_global x y =
  match (x, y) with
  | GFun x, GFun y -> equal_fundec x y
  | GVarDecl x, GVarDecl y -> equal_varinfo x y
  | GVar (vx, ix), GVar (vy, iy) ->
      equal_varinfo vx vy && equal_initinfo ix iy
  | (GFun _ | GVarDecl _ | GVar _), _ -> false

let equal_file x y =
  String.equal x.fileName y.fileName
  && equal_list equal_global x.globals y.globals
