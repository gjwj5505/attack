module S = Language.Syntax
module Check = Language.Check

let int_t = Language.Typ.TInt Language.Typ.IInt
let void_t = Language.Typ.TVoid

let var ?(vglob = false) ?(vtemp = false) name typ vid =
  { S.vname = name; vtype = typ; vglob; vtemp; vid }

let stmt skind = { S.labels = []; skind; sid = None }
let block bstmts = { S.bstmts }

let int_const n = S.Exp.Const (S.Exp.CInt (Int64.of_int n, Language.Typ.IInt))

let main_fun ?(ret = int_t) ?(formals = []) ?(locals = []) body =
  {
    S.svar = var ~vglob:true "main" ret 1;
    sformals = formals;
    slocals = locals;
    sbody = block body;
  }

let file globals = { S.fileName = "check-test.c"; globals }

let accept_minimal_main =
  (* Expected: Ok. Valid int main(void) returning 0. *)
  file [ S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]) ]

let reject_missing_main =
  (* Expected: Error Missing_main. No GFun named main exists. *)
  file []

let reject_multiple_main =
  (* Expected: Error Multiple_main. Two function definitions named main exist. *)
  file
    [
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
      S.GFun
        {
          S.svar = var ~vglob:true "main" int_t 2;
          sformals = [];
          slocals = [];
          sbody = block [ stmt (S.Return (Some (int_const 0))) ];
        };
    ]

let reject_invalid_main_type =
  (* Expected: Error (Invalid_main_type TVoid). main must return int. *)
  file [ S.GFun (main_fun ~ret:void_t [ stmt (S.Return None) ]) ]

let reject_main_with_parameters =
  (* Expected: Error Main_with_parameters. main must be int main(void). *)
  let argc = var "argc" int_t 2 in
  file
    [
      S.GFun
        (main_fun ~formals:[ argc ] [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let reject_duplicate_global_name =
  (* Expected: Error (Duplicate_global_name "g"). *)
  let g1 = var ~vglob:true "g" int_t 10 in
  let g2 = var ~vglob:true "g" int_t 11 in
  file
    [
      S.GVarDecl g1;
      S.GVarDecl g2;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let reject_duplicate_formal_name =
  (* Expected: Error duplicate local name in f: x. *)
  let x1 = var "x" int_t 30 in
  let x2 = var "x" int_t 31 in
  let f =
    {
      S.svar = var ~vglob:true "f" int_t 32;
      sformals = [ x1; x2 ];
      slocals = [];
      sbody = block [ stmt (S.Return (Some (int_const 0))) ];
    }
  in
  file
    [
      S.GFun f;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let reject_duplicate_local_name =
  (* Expected: Error duplicate local name in f: x. *)
  let x1 = var "x" int_t 33 in
  let x2 = var "x" int_t 34 in
  let f =
    {
      S.svar = var ~vglob:true "f" int_t 35;
      sformals = [];
      slocals = [ x1; x2 ];
      sbody = block [ stmt (S.Return (Some (int_const 0))) ];
    }
  in
  file
    [
      S.GFun f;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let reject_formal_local_name_collision =
  (* Expected: Error duplicate local name in f: x. *)
  let formal = var "x" int_t 36 in
  let local = var "x" int_t 37 in
  let f =
    {
      S.svar = var ~vglob:true "f" int_t 38;
      sformals = [ formal ];
      slocals = [ local ];
      sbody = block [ stmt (S.Return (Some (int_const 0))) ];
    }
  in
  file
    [
      S.GFun f;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let reject_break_outside_loop =
  (* Expected: Error Break_outside_loop. This AST cannot come from valid C
     source, but the synthesizer can construct it directly. *)
  file [ S.GFun (main_fun [ stmt S.Break; stmt (S.Return (Some (int_const 0))) ]) ]

let reject_continue_outside_loop =
  (* Expected: Error Continue_outside_loop. This AST cannot come from valid C
     source, but the synthesizer can construct it directly. *)
  file
    [ S.GFun (main_fun [ stmt S.Continue; stmt (S.Return (Some (int_const 0))) ]) ]

let reject_return_value_in_void_function =
  (* Expected: Error Return_value_in_void_function. Return expression presence
     must match the enclosing function return type. *)
  let f =
    {
      S.svar = var ~vglob:true "f" void_t 20;
      sformals = [];
      slocals = [];
      sbody = block [ stmt (S.Return (Some (int_const 1))) ];
    }
  in
  file
    [
      S.GFun f;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let reject_return_without_value_in_nonvoid_function =
  (* Expected: Error (Return_without_value_in_nonvoid_function int). Return
     expression presence must match the enclosing function return type. *)
  let f =
    {
      S.svar = var ~vglob:true "f" int_t 21;
      sformals = [];
      slocals = [];
      sbody = block [ stmt (S.Return None) ];
    }
  in
  file
    [
      S.GFun f;
      S.GFun (main_fun [ stmt (S.Return (Some (int_const 0))) ]);
    ]

let accept_break_continue_inside_loop =
  (* Expected: Ok. Break and continue are valid inside Loop. *)
  file
    [
      S.GFun
        (main_fun
           [
             stmt (S.Loop (block [ stmt S.Continue; stmt S.Break ]));
             stmt (S.Return (Some (int_const 0)));
           ]);
    ]

let expect_ok name f =
  match Check.check_file f with
  | Ok () -> ()
  | Error err ->
      failwith
        (Printf.sprintf "%s: expected Ok, got %s" name
           (Check.string_of_error err))

let expect_error name expected f =
  match Check.check_file f with
  | Error actual when actual = expected -> ()
  | Error actual ->
      failwith
        (Printf.sprintf "%s: expected %s, got %s" name
           (Check.string_of_error expected)
           (Check.string_of_error actual))
  | Ok () ->
      failwith
        (Printf.sprintf "%s: expected %s, got Ok" name
           (Check.string_of_error expected))

let () =
  let cases =
    [
      ("accept_minimal_main", fun () -> expect_ok "accept_minimal_main" accept_minimal_main);
      ("reject_missing_main", fun () ->
        expect_error "reject_missing_main" Check.Missing_main reject_missing_main);
      ("reject_multiple_main", fun () ->
        expect_error "reject_multiple_main" Check.Multiple_main reject_multiple_main);
      ("reject_invalid_main_type", fun () ->
        expect_error "reject_invalid_main_type"
          (Check.Invalid_main_type void_t)
          reject_invalid_main_type);
      ("reject_main_with_parameters", fun () ->
        expect_error "reject_main_with_parameters" Check.Main_with_parameters
          reject_main_with_parameters);
      ("reject_duplicate_global_name", fun () ->
        expect_error "reject_duplicate_global_name"
          (Check.Duplicate_global_name "g")
          reject_duplicate_global_name);
      ("reject_duplicate_formal_name", fun () ->
        expect_error "reject_duplicate_formal_name"
          (Check.Duplicate_function_local_name
             { function_name = "f"; name = "x" })
          reject_duplicate_formal_name);
      ("reject_duplicate_local_name", fun () ->
        expect_error "reject_duplicate_local_name"
          (Check.Duplicate_function_local_name
             { function_name = "f"; name = "x" })
          reject_duplicate_local_name);
      ("reject_formal_local_name_collision", fun () ->
        expect_error "reject_formal_local_name_collision"
          (Check.Duplicate_function_local_name
             { function_name = "f"; name = "x" })
          reject_formal_local_name_collision);
      ("reject_break_outside_loop", fun () ->
        expect_error "reject_break_outside_loop" Check.Break_outside_loop
          reject_break_outside_loop);
      ("reject_continue_outside_loop", fun () ->
        expect_error "reject_continue_outside_loop" Check.Continue_outside_loop
          reject_continue_outside_loop);
      ("reject_return_value_in_void_function", fun () ->
        expect_error "reject_return_value_in_void_function"
          Check.Return_value_in_void_function
          reject_return_value_in_void_function);
      ("reject_return_without_value_in_nonvoid_function", fun () ->
        expect_error "reject_return_without_value_in_nonvoid_function"
          (Check.Return_without_value_in_nonvoid_function int_t)
          reject_return_without_value_in_nonvoid_function);
      ("accept_break_continue_inside_loop", fun () ->
        expect_ok "accept_break_continue_inside_loop"
          accept_break_continue_inside_loop);
    ]
  in
  List.iter
    (fun (name, run) ->
      run ();
      Printf.printf "ok - %s\n" name)
    cases
