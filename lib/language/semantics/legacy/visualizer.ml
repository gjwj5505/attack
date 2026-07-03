open BigStep
open Syntax

type box = {
  lines : string list;
  width : int;
  height : int;
}

type side = Top | Bottom

let make_box s =
  let raw_lines = String.split_on_char '\n' s in
  let rec trim_empty = function
    | "" :: tl -> trim_empty tl
    | lines -> lines
  in
  let lines = raw_lines |> trim_empty |> List.rev |> trim_empty |> List.rev in
  let lines = if lines = [] then [ "" ] else lines in
  let width = List.fold_left (fun acc l -> max acc (String.length l)) 0 lines in
  { lines; width; height = List.length lines }

let empty_box = { lines = []; width = 0; height = 0 }

let pad side b target_h =
  let diff = target_h - b.height in
  if diff <= 0 then b.lines
  else
    let padding = List.init diff (fun _ -> String.make b.width ' ') in
    match side with
    | Top -> b.lines @ padding
    | Bottom -> padding @ b.lines

let block_summary block = Printf.sprintf "block[%d]" (List.length block)

let string_of_stmt_summary = function
  | Stmt.Decl (binding, exp) ->
      Printf.sprintf "%s = %s;" (string_of_binding binding) (Exp.string_of_t exp)
  | Stmt.Assign (lval, exp) ->
      Printf.sprintf "%s = %s;" (string_of_lval lval) (Exp.string_of_t exp)
  | Stmt.If (cond, _, _) ->
      Printf.sprintf "if (%s) {...} else {...}" (Exp.string_of_t cond)
  | Stmt.While (cond, _) ->
      Printf.sprintf "while (%s) {...}" (Exp.string_of_t cond)
  | Stmt.Return exp -> Printf.sprintf "return %s;" (Exp.string_of_t exp)

let rec string_of_stmt_verbose ?(lvl = 0) stmt =
  let pad = Stmt.indent lvl in
  match stmt with
  | Stmt.Decl (binding, exp) ->
      Printf.sprintf "%s%s = %s;" pad (string_of_binding binding)
        (Exp.string_of_t exp)
  | Stmt.Assign (lval, exp) ->
      Printf.sprintf "%s%s = %s;" pad (string_of_lval lval)
        (Exp.string_of_t exp)
  | Stmt.If (cond, then_block, else_block) ->
      Printf.sprintf "%sif (%s)\n%s\n%selse\n%s" pad (Exp.string_of_t cond)
        (string_of_block_verbose ~lvl:(lvl + 1) then_block)
        pad
        (string_of_block_verbose ~lvl:(lvl + 1) else_block)
  | Stmt.While (cond, body) ->
      Printf.sprintf "%swhile (%s)\n%s" pad (Exp.string_of_t cond)
        (string_of_block_verbose ~lvl:(lvl + 1) body)
  | Stmt.Return exp -> Printf.sprintf "%sreturn %s;" pad (Exp.string_of_t exp)

and string_of_block_verbose ?(lvl = 0) block =
  match block with
  | [] -> Stmt.indent lvl ^ "empty"
  | _ -> String.concat "\n" (List.map (string_of_stmt_verbose ~lvl) block)

let string_of_stmt ?(verbose = false) stmt =
  if verbose then string_of_stmt_verbose stmt else string_of_stmt_summary stmt

let string_of_block ?(verbose = false) block =
  if verbose then string_of_block_verbose block else block_summary block

let make_conclusion ?(verbose = false) mem_opt subject result =
  let boxes =
    match mem_opt with
    | Some mem when verbose ->
        [
          make_box (Memory.string_of_t mem);
          make_box "|-";
          make_box subject;
          make_box "=>";
          make_box result;
        ]
    | _ -> [ make_box subject; make_box "=>"; make_box result ]
  in
  let max_h = List.fold_left (fun acc b -> max acc b.height) 0 boxes in
  let adjusted_boxes =
    List.map
      (fun b ->
        {
          b with
          lines =
            List.map
              (fun s -> s ^ String.make (b.width - String.length s) ' ')
              (pad Top b max_h);
        })
      boxes
  in
  let combined_lines =
    List.init max_h (fun i ->
        String.concat " "
          (List.map (fun b -> List.nth b.lines i) adjusted_boxes))
  in
  let total_w =
    List.fold_left (fun acc b -> acc + b.width) 0 adjusted_boxes
    + List.length adjusted_boxes - 1
  in
  { lines = combined_lines; width = total_w; height = max_h }

let build_proof rule_name premises conclusion_box =
  let gap = 3 in
  let premise_box =
    match premises with
    | [] -> empty_box
    | [ p ] -> p
    | ps ->
        let max_ph = List.fold_left (fun acc b -> max acc b.height) 0 ps in
        let padded_ps =
          List.map
            (fun b -> { b with lines = pad Bottom b max_ph; height = max_ph })
            ps
        in
        List.fold_left
          (fun acc b ->
            let combined =
              List.map2
                (fun s1 s2 -> s1 ^ String.make gap ' ' ^ s2)
                acc.lines b.lines
            in
            {
              lines = combined;
              width = acc.width + gap + b.width;
              height = max_ph;
            })
          (List.hd padded_ps) (List.tl padded_ps)
  in
  let label = make_box (Printf.sprintf "[%s] " rule_name) in
  let full_h = max label.height conclusion_box.height in
  let conc_lines =
    List.map2 (fun label concl -> label ^ concl) (pad Top label full_h)
      (pad Top conclusion_box full_h)
  in
  let conc_box =
    {
      lines = conc_lines;
      width = label.width + conclusion_box.width;
      height = full_h;
    }
  in
  let max_w = max premise_box.width conc_box.width in
  let line = String.make max_w '-' in
  let center_lines b w =
    if b.width = 0 && b.height = 0 then []
    else
      let left_pad = (w - b.width) / 2 in
      let right_pad = w - b.width - left_pad in
      List.map
        (fun s -> String.make left_pad ' ' ^ s ^ String.make right_pad ' ')
        b.lines
  in
  let p_lines = center_lines premise_box max_w in
  let c_lines = center_lines conc_box max_w in
  {
    lines = p_lines @ [ line ] @ c_lines;
    width = max_w;
    height = List.length p_lines + 1 + List.length c_lines;
  }

let string_of_expr_result ?(verbose = false) out_mem value =
  if verbose then
    Printf.sprintf "%s / %s" (Memory.string_of_t out_mem) (Value.string_of_t value)
  else Value.string_of_t value

let string_of_stmt_result ?(verbose = false) out_mem control =
  if verbose then
    Printf.sprintf "%s / %s" (Memory.string_of_t out_mem)
      (BigStepUtil.string_of_control control)
  else BigStepUtil.string_of_control control

let string_of_program_result ?(verbose = false) out_mem value =
  if verbose then
    Printf.sprintf "%s / %s" (Memory.string_of_t out_mem) (Value.string_of_t value)
  else Value.string_of_t value

let e_conclusion ?(verbose = false) (mem, exp, out_mem, value) =
  make_conclusion ~verbose (Some mem) (Exp.string_of_t exp)
    (string_of_expr_result ~verbose out_mem value)

let s_conclusion ?(verbose = false) (mem, stmt, out_mem, control) =
  make_conclusion ~verbose (Some mem) (string_of_stmt ~verbose stmt)
    (string_of_stmt_result ~verbose out_mem control)

let b_conclusion ?(verbose = false) (mem, block, out_mem, control) =
  make_conclusion ~verbose (Some mem) (string_of_block ~verbose block)
    (string_of_stmt_result ~verbose out_mem control)

let p_conclusion ?(verbose = false) (_, out_mem, value) =
  make_conclusion ~verbose None "int main()"
    (string_of_program_result ~verbose out_mem value)

let rec box_of_etree ?(verbose = false) tree =
  match tree with
  | EIntLiteral (_, concl) ->
      build_proof "Int" [] (e_conclusion ~verbose concl)
  | ENegIntLiteral (_, concl) ->
      build_proof "NegInt" [] (e_conclusion ~verbose concl)
  | ELval (_, concl) ->
      build_proof "Lval" [] (e_conclusion ~verbose concl)
  | EUop (sub, concl) ->
      build_proof "Uop" [ box_of_etree ~verbose sub ]
        (e_conclusion ~verbose concl)
  | EBop ((left, right), concl) ->
      build_proof "Bop"
        [ box_of_etree ~verbose left; box_of_etree ~verbose right ]
        (e_conclusion ~verbose concl)
  | ELogicalOrLeftTrue (left, concl) ->
      build_proof "OrLT" [ box_of_etree ~verbose left ]
        (e_conclusion ~verbose concl)
  | ELogicalOrLeftFalse ((left, right), concl) ->
      build_proof "OrLF"
        [ box_of_etree ~verbose left; box_of_etree ~verbose right ]
        (e_conclusion ~verbose concl)
  | ELogicalAndLeftFalse (left, concl) ->
      build_proof "AndLF" [ box_of_etree ~verbose left ]
        (e_conclusion ~verbose concl)
  | ELogicalAndLeftTrue ((left, right), concl) ->
      build_proof "AndLT"
        [ box_of_etree ~verbose left; box_of_etree ~verbose right ]
        (e_conclusion ~verbose concl)

let rec box_of_stree ?(verbose = false) tree =
  match tree with
  | SDecl (exp, concl) ->
      build_proof "Decl" [ box_of_etree ~verbose exp ]
        (s_conclusion ~verbose concl)
  | SAssign (exp, concl) ->
      build_proof "Asgn" [ box_of_etree ~verbose exp ]
        (s_conclusion ~verbose concl)
  | SIfTrue ((cond, body), concl) ->
      build_proof "IfT"
        [ box_of_etree ~verbose cond; box_of_btree ~verbose body ]
        (s_conclusion ~verbose concl)
  | SIfFalse ((cond, body), concl) ->
      build_proof "IfF"
        [ box_of_etree ~verbose cond; box_of_btree ~verbose body ]
        (s_conclusion ~verbose concl)
  | SWhileFalse (cond, concl) ->
      build_proof "WhlF" [ box_of_etree ~verbose cond ]
        (s_conclusion ~verbose concl)
  | SWhileTrueNormal ((cond, body, rest), concl) ->
      build_proof "WhlN"
        [
          box_of_etree ~verbose cond;
          box_of_btree ~verbose body;
          box_of_stree ~verbose rest;
        ]
        (s_conclusion ~verbose concl)
  | SWhileTrueContinue ((cond, body, rest), concl) ->
      build_proof "WhlC"
        [
          box_of_etree ~verbose cond;
          box_of_btree ~verbose body;
          box_of_stree ~verbose rest;
        ]
        (s_conclusion ~verbose concl)
  | SWhileTrueBreak ((cond, body), concl) ->
      build_proof "WhlB"
        [ box_of_etree ~verbose cond; box_of_btree ~verbose body ]
        (s_conclusion ~verbose concl)
  | SWhileTrueReturn ((cond, body), concl) ->
      build_proof "WhlR"
        [ box_of_etree ~verbose cond; box_of_btree ~verbose body ]
        (s_conclusion ~verbose concl)
  | SReturn (exp, concl) ->
      build_proof "Ret" [ box_of_etree ~verbose exp ]
        (s_conclusion ~verbose concl)

and box_of_btree ?(verbose = false) tree =
  match tree with
  | BEmpty concl -> build_proof "BEmp" [] (b_conclusion ~verbose concl)
  | BSeqNormal ((stmt, rest), concl) ->
      build_proof "BSeqN"
        [ box_of_stree ~verbose stmt; box_of_btree ~verbose rest ]
        (b_conclusion ~verbose concl)
  | BSeqReturn (stmt, concl) ->
      build_proof "BSeqR" [ box_of_stree ~verbose stmt ]
        (b_conclusion ~verbose concl)
  | BSeqBreak (stmt, concl) ->
      build_proof "BSeqB" [ box_of_stree ~verbose stmt ]
        (b_conclusion ~verbose concl)
  | BSeqContinue (stmt, concl) ->
      build_proof "BSeqC" [ box_of_stree ~verbose stmt ]
        (b_conclusion ~verbose concl)

let box_of_ptree ?(verbose = false) = function
  | PMainReturn (body, concl) ->
      build_proof "Main" [ box_of_btree ~verbose body ]
        (p_conclusion ~verbose concl)

let print_tree ?(verbose = false) tree =
  let final_box =
    match tree with
    | ETree t -> box_of_etree ~verbose t
    | STree t -> box_of_stree ~verbose t
    | BTree t -> box_of_btree ~verbose t
    | PTree t -> box_of_ptree ~verbose t
  in
  List.iter print_endline final_box.lines

let render_tree ?(verbose = false) tree =
  let final_box =
    match tree with
    | ETree t -> box_of_etree ~verbose t
    | STree t -> box_of_stree ~verbose t
    | BTree t -> box_of_btree ~verbose t
    | PTree t -> box_of_ptree ~verbose t
  in
  final_box.lines

let write_tree_svg ?(verbose = false) path tree =
  render_tree ~verbose tree |> TextSvg.write_lines path
