open Language

module S = Syntax

let int_t = Typ.TInt Typ.IInt

let var ?(vglob = false) name typ vid =
  { S.vname = name; vtype = typ; vglob; vtemp = false; vid }

let stmt skind = { S.labels = []; skind; sid = None }
let block bstmts = { S.bstmts }
let int_exp n = S.Const (S.CInt (Int64.of_int n, Typ.IInt))
let lval v = (S.Var v, S.NoOffset)
let var_exp v = S.Lval (lval v)

let build_file () =
  let main_var = var ~vglob:true "main" int_t 1 in
  let x = var "x" int_t 2 in
  let cond = S.BinOp (S.Eq, var_exp x, int_exp 0, int_t) in
  let dec = S.BinOp (S.MinusA, var_exp x, int_exp 1, int_t) in
  let body =
    block
      [
        stmt (S.If (cond, block [ stmt S.Break ], block []));
        stmt (S.Instr [ S.Set (lval x, dec) ]);
      ]
  in
  let main =
    {
      S.svar = main_var;
      sformals = [];
      slocals = [ x ];
      sbody =
        block
          [
            stmt (S.Instr [ S.Set (lval x, int_exp 2) ]);
            stmt (S.Loop body);
            stmt (S.Return (Some (var_exp x)));
          ];
    }
  in
  { S.fileName = "manual-countdown-loop.cil"; globals = [ S.GFun main ] }

let ensure_dir path = if Sys.file_exists path then () else Sys.mkdir path 0o755

let () =
  let file = build_file () in
  print_endline "CIL' AST:";
  SyntaxTree.print_file file;
  match Check.check_file file with
  | Error err ->
      prerr_endline (Check.string_of_error err);
      exit 1
  | Ok () -> (
      match Derivator.derive_file file with
      | Error err ->
          prerr_endline (Derivator.string_of_error err);
          exit 1
      | Ok tree ->
          begin
            match BigStepChecker.check_ptree ~check_file:false tree with
            | BigStepChecker.Valid -> ()
            | BigStepChecker.Invalid msg ->
                prerr_endline ("invalid Big-Step tree: " ^ msg);
                exit 1
          end;
          let BigStep.PTreeMainReturn (_, (_, _, value)) = tree in
          let size = Size.sizeof_tree (BigStep.PTree tree) in
          ensure_dir "dist";
          ensure_dir "dist/proofs";
          let svg_path = "dist/proofs/manual_countdown_loop.svg" in
          Visualizer.write_tree_svg svg_path (BigStep.PTree tree);
          Printf.printf
            "\nBig-Step tree constructed and checked. main returned %s\nSize %s\nSVG written to %s\n"
            (Value.string_of_t value) (Size.to_string size) svg_path )
