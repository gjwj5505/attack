module Cil = GoblintCil.Cil
module Cilint = GoblintCil.Cilint
module Frontc = GoblintCil.Frontc
module Pretty = GoblintCil.Pretty

module S = Syntax

type unsupported = {
  feature : string;
}

type error =
  | Parse_error of string
  | Unsupported of unsupported

let unsupported feature = Error (Unsupported { feature })

let ( let* ) = Result.bind

let rec list_map_result f = function
  | [] -> Ok []
  | x :: xs ->
      let* y = f x in
      let* ys = list_map_result f xs in
      Ok (y :: ys)

let parse_c_file path =
  try Ok (Frontc.parse path ())
  with
  | Frontc.ParseError msg -> Error (Parse_error msg)
  | Failure msg -> Error (Parse_error msg)

let typ_to_cil = function
  | Typ.Int -> Cil.intType

let typ_of_cil typ =
  match Cil.unrollTypeDeep typ with
  | Cil.TInt (Cil.IInt, _) -> Ok Typ.Int
  | typ ->
      unsupported
        ("non-int type: " ^ Pretty.sprint ~width:80 (Cil.d_type () typ))

let varinfo_to_cil v =
  let vi = Cil.makeVarinfo v.S.vglob v.vname (typ_to_cil v.vtype) in
  vi.Cil.vid <- v.vid;
  vi

let fundec_svar_to_cil f =
  let formals =
    List.map
      (fun v -> (v.S.vname, typ_to_cil v.S.vtype, []))
      f.S.sformals
  in
  let typ = Cil.TFun (typ_to_cil f.S.svar.S.vtype, Some formals, false, []) in
  let vi = Cil.makeGlobalVar f.S.svar.S.vname typ in
  vi.Cil.vid <- f.S.svar.S.vid;
  vi

let varinfo_of_cil vi =
  let* vtype = typ_of_cil vi.Cil.vtype in
  Ok
    {
      S.vname = vi.Cil.vname;
      vtype;
      vglob = vi.Cil.vglob;
      vtemp = false;
      vid = vi.Cil.vid;
    }

let fundec_svar_of_cil vi =
  match Cil.unrollTypeDeep vi.Cil.vtype with
  | Cil.TFun (ret_typ, _, false, _) ->
      let* vtype = typ_of_cil ret_typ in
      Ok
        {
          S.vname = vi.Cil.vname;
          vtype;
          vglob = vi.Cil.vglob;
          vtemp = false;
          vid = vi.Cil.vid;
        }
  | Cil.TFun (_, _, true, _) -> unsupported "varargs function"
  | _ -> unsupported "non-function svar"

let lval_to_cil var_tbl = function
  | S.Var v -> (
      match Hashtbl.find_opt var_tbl v.S.vid with
      | Some vi -> Ok (Cil.Var vi, Cil.NoOffset)
      | None ->
          let vi = varinfo_to_cil v in
          Hashtbl.add var_tbl v.S.vid vi;
          Ok (Cil.Var vi, Cil.NoOffset) )

let lval_of_cil = function
  | Cil.Var vi, Cil.NoOffset ->
      let* vi = varinfo_of_cil vi in
      Ok (S.Var vi)
  | Cil.Mem _, _ -> unsupported "memory lvalue"
  | Cil.Var _, (Cil.Field _ | Cil.Index _) -> unsupported "lvalue offset"

let constant_to_cil = function
  | S.Exp.CInt64 n -> Cil.CInt (Cilint.cilint_of_int64 n, Cil.IInt, None)

let constant_of_cil = function
  | Cil.CInt (n, Cil.IInt, _) -> Ok (S.Exp.CInt64 (Cilint.int64_of_cilint n))
  | Cil.CInt _ -> unsupported "non-int integer constant"
  | Cil.CStr _ -> unsupported "string constant"
  | Cil.CWStr _ -> unsupported "wide string constant"
  | Cil.CChr _ -> unsupported "character constant"
  | Cil.CReal _ -> unsupported "real constant"
  | Cil.CEnum _ -> unsupported "enum constant"

let unop_to_cil = function
  | S.Exp.Neg -> Cil.Neg
  | S.Exp.BNot -> Cil.BNot
  | S.Exp.LNot -> Cil.LNot

let unop_of_cil = function
  | Cil.Neg -> Ok S.Exp.Neg
  | Cil.BNot -> Ok S.Exp.BNot
  | Cil.LNot -> Ok S.Exp.LNot

let binop_to_cil = function
  | S.Exp.PlusA -> Cil.PlusA
  | S.Exp.MinusA -> Cil.MinusA
  | S.Exp.Mult -> Cil.Mult
  | S.Exp.Div -> Cil.Div
  | S.Exp.Mod -> Cil.Mod
  | S.Exp.Lt -> Cil.Lt
  | S.Exp.Gt -> Cil.Gt
  | S.Exp.Le -> Cil.Le
  | S.Exp.Ge -> Cil.Ge
  | S.Exp.Eq -> Cil.Eq
  | S.Exp.Ne -> Cil.Ne
  | S.Exp.BAnd -> Cil.BAnd
  | S.Exp.BXor -> Cil.BXor
  | S.Exp.BOr -> Cil.BOr
  | S.Exp.LAnd -> Cil.LAnd
  | S.Exp.LOr -> Cil.LOr
  | S.Exp.Shiftlt -> Cil.Shiftlt
  | S.Exp.Shiftrt -> Cil.Shiftrt

let binop_of_cil = function
  | Cil.PlusA -> Ok S.Exp.PlusA
  | Cil.MinusA -> Ok S.Exp.MinusA
  | Cil.Mult -> Ok S.Exp.Mult
  | Cil.Div -> Ok S.Exp.Div
  | Cil.Mod -> Ok S.Exp.Mod
  | Cil.Lt -> Ok S.Exp.Lt
  | Cil.Gt -> Ok S.Exp.Gt
  | Cil.Le -> Ok S.Exp.Le
  | Cil.Ge -> Ok S.Exp.Ge
  | Cil.Eq -> Ok S.Exp.Eq
  | Cil.Ne -> Ok S.Exp.Ne
  | Cil.BAnd -> Ok S.Exp.BAnd
  | Cil.BXor -> Ok S.Exp.BXor
  | Cil.BOr -> Ok S.Exp.BOr
  | Cil.LAnd -> Ok S.Exp.LAnd
  | Cil.LOr -> Ok S.Exp.LOr
  | Cil.Shiftlt -> Ok S.Exp.Shiftlt
  | Cil.Shiftrt -> Ok S.Exp.Shiftrt
  | Cil.PlusPI -> unsupported "pointer addition"
  | Cil.IndexPI -> unsupported "pointer index addition"
  | Cil.MinusPI -> unsupported "pointer subtraction"
  | Cil.MinusPP -> unsupported "pointer difference"

let rec exp_to_cil var_tbl = function
  | S.Exp.Const c -> Ok (Cil.Const (constant_to_cil c))
  | S.Exp.Lval lv ->
      let* lv = lval_to_cil var_tbl lv in
      Ok (Cil.Lval lv)
  | S.Exp.UnOp (op, e, typ) ->
      let* e = exp_to_cil var_tbl e in
      Ok (Cil.UnOp (unop_to_cil op, e, typ_to_cil typ))
  | S.Exp.BinOp (op, e1, e2, typ) ->
      let* e1 = exp_to_cil var_tbl e1 in
      let* e2 = exp_to_cil var_tbl e2 in
      Ok (Cil.BinOp (binop_to_cil op, e1, e2, typ_to_cil typ))
  | S.Exp.CastE (typ, e) ->
      let* e = exp_to_cil var_tbl e in
      Ok (Cil.CastE (typ_to_cil typ, e))

let rec exp_of_cil = function
  | Cil.Const c ->
      let* c = constant_of_cil c in
      Ok (S.Exp.Const c)
  | Cil.Lval lv ->
      let* lv = lval_of_cil lv in
      Ok (S.Exp.Lval lv)
  | Cil.UnOp (op, e, typ) ->
      let* op = unop_of_cil op in
      let* e = exp_of_cil e in
      let* typ = typ_of_cil typ in
      Ok (S.Exp.UnOp (op, e, typ))
  | Cil.BinOp (op, e1, e2, typ) ->
      let* op = binop_of_cil op in
      let* e1 = exp_of_cil e1 in
      let* e2 = exp_of_cil e2 in
      let* typ = typ_of_cil typ in
      Ok (S.Exp.BinOp (op, e1, e2, typ))
  | Cil.CastE (typ, e) ->
      let* typ = typ_of_cil typ in
      let* e = exp_of_cil e in
      Ok (S.Exp.CastE (typ, e))
  | Cil.SizeOf _ -> unsupported "sizeof type expression"
  | Cil.Real _ -> unsupported "real-part expression"
  | Cil.Imag _ -> unsupported "imaginary-part expression"
  | Cil.SizeOfE _ -> unsupported "sizeof expression"
  | Cil.SizeOfStr _ -> unsupported "sizeof string"
  | Cil.AlignOf _ -> unsupported "alignof type expression"
  | Cil.AlignOfE _ -> unsupported "alignof expression"
  | Cil.Question _ -> unsupported "conditional expression"
  | Cil.AddrOf _ -> unsupported "address-of expression"
  | Cil.AddrOfLabel _ -> unsupported "address-of-label expression"
  | Cil.StartOf _ -> unsupported "array start expression"

let instr_to_cil var_tbl = function
  | S.Set (lv, e) ->
      let* lv = lval_to_cil var_tbl lv in
      let* e = exp_to_cil var_tbl e in
      Ok (Cil.Set (lv, e, Cil.locUnknown, Cil.locUnknown))

let instr_of_cil = function
  | Cil.Set (lv, e, _, _) ->
      let* lv = lval_of_cil lv in
      let* e = exp_of_cil e in
      Ok (S.Set (lv, e))
  | Cil.VarDecl _ -> unsupported "var declaration instruction"
  | Cil.Call _ -> unsupported "call instruction"
  | Cil.Asm _ -> unsupported "asm instruction"

let label_to_cil = function
  | S.Label name -> Cil.Label (name, Cil.locUnknown, false)

let label_of_cil = function
  | Cil.Label (name, _, _) -> Ok (S.Label name)
  | Cil.Case _ -> unsupported "case label"
  | Cil.CaseRange _ -> unsupported "case range label"
  | Cil.Default _ -> unsupported "default label"

let rec block_to_cil var_tbl block =
  let* stmts = list_map_result (stmt_to_cil var_tbl) block.S.bstmts in
  Ok (Cil.mkBlock stmts)

and stmt_to_cil var_tbl stmt =
  let* skind = stmtkind_to_cil var_tbl stmt.S.skind in
  let cil_stmt = Cil.mkStmt skind in
  cil_stmt.Cil.labels <- List.map label_to_cil stmt.S.labels;
  (match stmt.S.sid with Some sid -> cil_stmt.Cil.sid <- sid | None -> ());
  Ok cil_stmt

and stmtkind_to_cil var_tbl = function
  | S.Instr instrs ->
      let* instrs = list_map_result (instr_to_cil var_tbl) instrs in
      Ok (Cil.Instr instrs)
  | S.Return e ->
      let* e =
        match e with
        | None -> Ok None
        | Some e ->
            let* e = exp_to_cil var_tbl e in
            Ok (Some e)
      in
      Ok (Cil.Return (e, Cil.locUnknown, Cil.locUnknown))
  | S.If (cond, tb, fb) ->
      let* cond = exp_to_cil var_tbl cond in
      let* tb = block_to_cil var_tbl tb in
      let* fb = block_to_cil var_tbl fb in
      Ok (Cil.If (cond, tb, fb, Cil.locUnknown, Cil.locUnknown))
  | S.Loop body ->
      let* body = block_to_cil var_tbl body in
      Ok (Cil.Loop (body, Cil.locUnknown, Cil.locUnknown, None, None))
  | S.Break -> Ok (Cil.Break Cil.locUnknown)
  | S.Continue -> Ok (Cil.Continue Cil.locUnknown)
  | S.Block block ->
      let* block = block_to_cil var_tbl block in
      Ok (Cil.Block block)

and block_of_cil block =
  let* bstmts = list_map_result stmt_of_cil block.Cil.bstmts in
  Ok { S.bstmts }

and stmt_of_cil stmt =
  let* labels = list_map_result label_of_cil stmt.Cil.labels in
  let* skind = stmtkind_of_cil stmt.Cil.skind in
  Ok { S.labels; skind; sid = Some stmt.Cil.sid }

and stmtkind_of_cil = function
  | Cil.Instr instrs ->
      let* instrs = list_map_result instr_of_cil instrs in
      Ok (S.Instr instrs)
  | Cil.Return (e, _, _) ->
      let* e =
        match e with
        | None -> Ok None
        | Some e ->
            let* e = exp_of_cil e in
            Ok (Some e)
      in
      Ok (S.Return e)
  | Cil.If (cond, tb, fb, _, _) ->
      let* cond = exp_of_cil cond in
      let* tb = block_of_cil tb in
      let* fb = block_of_cil fb in
      Ok (S.If (cond, tb, fb))
  | Cil.Loop (body, _, _, _, _) ->
      let* body = block_of_cil body in
      Ok (S.Loop body)
  | Cil.Break _ -> Ok S.Break
  | Cil.Continue _ -> Ok S.Continue
  | Cil.Block block ->
      let* block = block_of_cil block in
      Ok (S.Block block)
  | Cil.Goto _ -> unsupported "goto statement"
  | Cil.ComputedGoto _ -> unsupported "computed goto statement"
  | Cil.Switch _ -> unsupported "switch statement"

let fundec_to_cil f =
  let var_tbl = Hashtbl.create 16 in
  let svar = fundec_svar_to_cil f in
  Hashtbl.add var_tbl f.S.svar.S.vid svar;
  let sformals = List.map varinfo_to_cil f.S.sformals in
  let slocals = List.map varinfo_to_cil f.S.slocals in
  List.iter (fun vi -> Hashtbl.replace var_tbl vi.Cil.vid vi) sformals;
  List.iter (fun vi -> Hashtbl.replace var_tbl vi.Cil.vid vi) slocals;
  let* sbody = block_to_cil var_tbl f.S.sbody in
  let fd = Cil.emptyFunction f.S.svar.S.vname in
  fd.Cil.svar <- svar;
  fd.Cil.sformals <- sformals;
  fd.Cil.slocals <- slocals;
  fd.Cil.sbody <- sbody;
  Ok fd

let fundec_of_cil fd =
  let* svar = fundec_svar_of_cil fd.Cil.svar in
  let* sformals = list_map_result varinfo_of_cil fd.Cil.sformals in
  let* slocals = list_map_result varinfo_of_cil fd.Cil.slocals in
  let* sbody = block_of_cil fd.Cil.sbody in
  Ok { S.svar; sformals; slocals; sbody }

let global_to_cil = function
  | S.GFun f ->
      let* f = fundec_to_cil f in
      Ok (Cil.GFun (f, Cil.locUnknown))
  | S.GVarDecl v ->
      Ok (Cil.GVarDecl (varinfo_to_cil v, Cil.locUnknown))

let global_of_cil = function
  | Cil.GFun (fd, _) ->
      let* fd = fundec_of_cil fd in
      Ok (S.GFun fd)
  | Cil.GVarDecl (vi, _) ->
      let* vi = varinfo_of_cil vi in
      Ok (S.GVarDecl vi)
  | Cil.GType _ -> unsupported "typedef global"
  | Cil.GCompTag _ -> unsupported "compound tag global"
  | Cil.GCompTagDecl _ -> unsupported "compound tag declaration global"
  | Cil.GEnumTag _ -> unsupported "enum tag global"
  | Cil.GEnumTagDecl _ -> unsupported "enum tag declaration global"
  | Cil.GVar _ -> unsupported "global variable definition"
  | Cil.GAsm _ -> unsupported "global asm"
  | Cil.GPragma _ -> unsupported "global pragma"
  | Cil.GText _ -> unsupported "global text"

let file_to_cil file =
  let* globals = list_map_result global_to_cil file.S.globals in
  Ok { Cil.dummyFile with Cil.fileName = file.S.fileName; globals }

let file_of_cil file =
  let* globals = list_map_result global_of_cil file.Cil.globals in
  Ok { S.fileName = file.Cil.fileName; globals }

let program_of_file file =
  let rec find_main = function
    | [] -> unsupported "missing main function"
    | S.GFun fd :: _ when fd.S.svar.S.vname = "main" -> Ok { S.main = fd }
    | _ :: rest -> find_main rest
  in
  find_main file.S.globals

let program_of_cil_file file =
  let rec find_main = function
    | [] -> unsupported "missing main function"
    | Cil.GFun (fd, _) :: _ when fd.Cil.svar.Cil.vname = "main" ->
        let* main = fundec_of_cil fd in
        Ok { S.main }
    | _ :: rest -> find_main rest
  in
  find_main file.Cil.globals

let parse_c_file_as_file path =
  let* cil_file = parse_c_file path in
  file_of_cil cil_file

let parse_c_file_as_program path =
  let* cil_file = parse_c_file path in
  program_of_cil_file cil_file

let cil_file_to_string cil_file =
  let tmp = Filename.temp_file "attack-cil-" ".c" in
  Fun.protect
    ~finally:(fun () -> Sys.remove tmp)
    (fun () ->
      let oc = open_out tmp in
      Fun.protect
        ~finally:(fun () -> close_out_noerr oc)
        (fun () -> Cil.dumpFile Cil.defaultCilPrinter oc cil_file.Cil.fileName cil_file);
      let ic = open_in tmp in
      Fun.protect
        ~finally:(fun () -> close_in_noerr ic)
        (fun () -> really_input_string ic (in_channel_length ic)))

let string_of_file file =
  let* cil_file = file_to_cil file in
  Ok (cil_file_to_string cil_file)

let string_of_program program =
  let file =
    {
      S.fileName = program.S.main.S.svar.S.vname ^ ".c";
      globals = [ S.GFun program.S.main ];
    }
  in
  string_of_file file

let write_file oc file =
  let* cil_file = file_to_cil file in
  Cil.dumpFile Cil.defaultCilPrinter oc cil_file.Cil.fileName cil_file;
  Ok ()

let write_program oc program =
  let file =
    {
      S.fileName = program.S.main.S.svar.S.vname ^ ".c";
      globals = [ S.GFun program.S.main ];
    }
  in
  write_file oc file

let string_of_error = function
  | Parse_error msg -> "CIL parse error: " ^ msg
  | Unsupported { feature } -> "unsupported CIL feature: " ^ feature
