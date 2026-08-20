open BigStep
open BigStepUtil
open Syntax

type box = {
  lines : string list;
  width : int;
  height : int;
}

type side =
  | Top
  | Bottom

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

let pad_lines b lines =
  List.map (fun s -> s ^ String.make (b.width - String.length s) ' ') lines

let make_conclusion ?(verbose = false) mem subject result =
  let boxes =
    if verbose then
      [ make_box (Memory.string_of_t mem); make_box "|-"; make_box subject; make_box "=>"; make_box result ]
    else [ make_box subject; make_box "=>"; make_box result ]
  in
  let max_h = List.fold_left (fun acc b -> max acc b.height) 0 boxes in
  let adjusted_boxes =
    List.map
      (fun b -> { b with lines = pad_lines b (pad Top b max_h); height = max_h })
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

let make_conclusion_no_mem subject result =
  let boxes = [ make_box subject; make_box "=>"; make_box result ] in
  let combined_lines =
    [ String.concat " " (List.map (fun b -> List.hd b.lines) boxes) ]
  in
  let total_w =
    List.fold_left (fun acc b -> acc + b.width) 0 boxes
    + List.length boxes - 1
  in
  { lines = combined_lines; width = total_w; height = 1 }

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

let string_of_exp = Syntax.Exp.string_of_t
let string_of_lval = Syntax.string_of_lval
let string_of_instr = Syntax.string_of_instr

let string_of_stmt_summary stmt =
  match stmt.Syntax.skind with
  | Instr instrs -> Printf.sprintf "instr[%d]" (List.length instrs)
  | Return None -> "return;"
  | Return (Some exp) -> "return " ^ string_of_exp exp ^ ";"
  | If (cond, _, _) -> Printf.sprintf "if (%s) {...}" (string_of_exp cond)
  | Loop _ -> "loop {...}"
  | Break -> "break;"
  | Continue -> "continue;"
  | Block block -> Printf.sprintf "block[%d]" (List.length block.bstmts)

let string_of_stmt ?(verbose = false) stmt =
  if verbose then Syntax.string_of_stmt stmt else string_of_stmt_summary stmt

let string_of_block ?(verbose = false) block =
  if verbose then Syntax.string_of_block block
  else Printf.sprintf "block[%d]" (List.length block.Syntax.bstmts)

let string_of_exp_result value = Value.string_of_t value
let string_of_lval_result loc = Location.string_of_t loc
let string_of_instr_result mem = Memory.string_of_t mem
let string_of_control_result control = string_of_control control
let string_of_function_subject fd = SyntaxUtil.var_name fd.Syntax.svar ^ "()"

let e_conclusion ?(verbose = false) (mem, exp, value) =
  make_conclusion ~verbose mem (string_of_exp exp) (string_of_exp_result value)

let l_conclusion ?(verbose = false) (mem, lval, loc) =
  make_conclusion ~verbose mem (string_of_lval lval) (string_of_lval_result loc)

let i_conclusion ?(verbose = false) (mem, instr, out_mem) =
  make_conclusion ~verbose mem (string_of_instr instr) (string_of_instr_result out_mem)

let s_conclusion ?(verbose = false) (mem, stmt, _out_mem, control) =
  make_conclusion ~verbose mem (string_of_stmt ~verbose stmt)
    (string_of_control_result control)

let b_conclusion ?(verbose = false) (mem, block, _out_mem, control) =
  make_conclusion ~verbose mem (string_of_block ~verbose block)
    (string_of_control_result control)

let f_conclusion ?(verbose = false) (mem, fd, _args, _out_mem, control) =
  make_conclusion ~verbose mem (string_of_function_subject fd)
    (string_of_control_result control)

let p_conclusion (_, _out_mem, value) =
  make_conclusion_no_mem "main()" (Value.string_of_t value)

let rec box_of_etree ?(verbose = false) tree =
  match tree with
  | ETreeConst concl -> build_proof "EConst" [] (e_conclusion ~verbose concl)
  | ETreeLval (ltree, concl) ->
      build_proof "ELval" [ box_of_ltree ~verbose ltree ]
        (e_conclusion ~verbose concl)
  | ETreeUnOp (sub, concl) ->
      build_proof "EUnOp" [ box_of_etree ~verbose sub ]
        (e_conclusion ~verbose concl)
  | ETreeLogicalOrLeftTrue (left, concl) ->
      build_proof "EOrT" [ box_of_etree ~verbose left ]
        (e_conclusion ~verbose concl)
  | ETreeLogicalOrLeftFalse (left, right, concl) ->
      build_proof "EOrF"
        [ box_of_etree ~verbose left; box_of_etree ~verbose right ]
        (e_conclusion ~verbose concl)
  | ETreeLogicalAndLeftFalse (left, concl) ->
      build_proof "EAndF" [ box_of_etree ~verbose left ]
        (e_conclusion ~verbose concl)
  | ETreeLogicalAndLeftTrue (left, right, concl) ->
      build_proof "EAndT"
        [ box_of_etree ~verbose left; box_of_etree ~verbose right ]
        (e_conclusion ~verbose concl)
  | ETreeBinOp (left, right, concl) ->
      build_proof "EBinOp"
        [ box_of_etree ~verbose left; box_of_etree ~verbose right ]
        (e_conclusion ~verbose concl)
  | ETreeAddrOf (ltree, concl) ->
      build_proof "EAddrOf" [ box_of_ltree ~verbose ltree ]
        (e_conclusion ~verbose concl)
  | ETreeStartOf (ltree, concl) ->
      build_proof "EStartOf" [ box_of_ltree ~verbose ltree ]
        (e_conclusion ~verbose concl)

and box_of_ltree ?(verbose = false) tree =
  match tree with
  | LTreeVar concl -> build_proof "LVar" [] (l_conclusion ~verbose concl)
  | LTreeMem (etree, concl) ->
      build_proof "LMem" [ box_of_etree ~verbose etree ]
        (l_conclusion ~verbose concl)
  | LTreeIndex (base, index, concl) ->
      build_proof "LIndex"
        [ box_of_ltree ~verbose base; box_of_etree ~verbose index ]
        (l_conclusion ~verbose concl)

let box_of_callee = function
  | CalleeTreeDirect (exp, _var, fd) ->
      build_proof "Callee" []
        (make_conclusion_no_mem (string_of_exp exp)
           (SyntaxUtil.var_name fd.Syntax.svar))

let rec box_of_itree ?(verbose = false) tree =
  match tree with
  | ITreeSet (ltree, etree, concl) ->
      build_proof "ISet"
        [ box_of_ltree ~verbose ltree; box_of_etree ~verbose etree ]
        (i_conclusion ~verbose concl)
  | ITreeCallVoid (callee, args, ftree, concl) ->
      build_proof "ICallVoid"
        (box_of_callee callee
        :: List.map (box_of_etree ~verbose) args
        @ [ box_of_ftree ~verbose ftree ])
        (i_conclusion ~verbose concl)
  | ITreeCallAssign (ltree, callee, args, ftree, concl) ->
      build_proof "ICallAssign"
        (box_of_ltree ~verbose ltree
        :: box_of_callee callee
        :: List.map (box_of_etree ~verbose) args
        @ [ box_of_ftree ~verbose ftree ])
        (i_conclusion ~verbose concl)

and box_of_stree ?(verbose = false) tree =
  match tree with
  | STreeInstr (itrees, concl) ->
      build_proof "SInstr" (List.map (box_of_itree ~verbose) itrees)
        (s_conclusion ~verbose concl)
  | STreeReturnNone concl ->
      build_proof "SReturnNone" [] (s_conclusion ~verbose concl)
  | STreeReturnSome (etree, concl) ->
      build_proof "SReturnSome" [ box_of_etree ~verbose etree ]
        (s_conclusion ~verbose concl)
  | STreeBreak concl -> build_proof "SBreak" [] (s_conclusion ~verbose concl)
  | STreeContinue concl ->
      build_proof "SContinue" [] (s_conclusion ~verbose concl)
  | STreeIfTrue (cond, body, concl) ->
      build_proof "SIfTrue"
        [ box_of_etree ~verbose cond; box_of_btree ~verbose body ]
        (s_conclusion ~verbose concl)
  | STreeIfFalse (cond, body, concl) ->
      build_proof "SIfFalse"
        [ box_of_etree ~verbose cond; box_of_btree ~verbose body ]
        (s_conclusion ~verbose concl)
  | STreeLoopRepeat (body, rest, concl) ->
      build_proof "SLoopRepeat"
        [ box_of_btree ~verbose body; box_of_stree ~verbose rest ]
        (s_conclusion ~verbose concl)
  | STreeLoopContinue (body, rest, concl) ->
      build_proof "SLoopContinue"
        [ box_of_btree ~verbose body; box_of_stree ~verbose rest ]
        (s_conclusion ~verbose concl)
  | STreeLoopBreak (body, concl) ->
      build_proof "SLoopBreak" [ box_of_btree ~verbose body ]
        (s_conclusion ~verbose concl)
  | STreeLoopReturn (body, concl) ->
      build_proof "SLoopReturn" [ box_of_btree ~verbose body ]
        (s_conclusion ~verbose concl)
  | STreeBlock (body, concl) ->
      build_proof "SBlock" [ box_of_btree ~verbose body ]
        (s_conclusion ~verbose concl)

and box_of_btree ?(verbose = false) tree =
  match tree with
  | BTreeSeq (strees, concl) ->
      build_proof "BSeq" (List.map (box_of_stree ~verbose) strees)
        (b_conclusion ~verbose concl)

and box_of_ftree ?(verbose = false) tree =
  match tree with
  | FTreeReturn (body, concl) ->
      build_proof "FReturn" [ box_of_btree ~verbose body ]
        (f_conclusion ~verbose concl)
  | FTreeNoReturn (body, concl) ->
      build_proof "FNoReturn" [ box_of_btree ~verbose body ]
        (f_conclusion ~verbose concl)

let box_of_ptree ?(verbose = false) = function
  | PTreeMainReturn (ftree, concl) as ptree ->
      let rule_name =
        Printf.sprintf "PMainReturn proof size %s"
          (Size.to_string (ProofSize.sizeof_tree (PTree ptree)))
      in
      build_proof rule_name [ box_of_ftree ~verbose ftree ]
        (p_conclusion concl)

let box_of_tree ?(verbose = false) = function
  | ETree t -> box_of_etree ~verbose t
  | LTree t -> box_of_ltree ~verbose t
  | ITree t -> box_of_itree ~verbose t
  | STree t -> box_of_stree ~verbose t
  | BTree t -> box_of_btree ~verbose t
  | FTree t -> box_of_ftree ~verbose t
  | PTree t -> box_of_ptree ~verbose t

let render_tree ?(verbose = false) tree = (box_of_tree ~verbose tree).lines

let print_tree ?(verbose = false) tree =
  render_tree ~verbose tree |> List.iter print_endline

let write_tree_svg ?(verbose = false) path tree =
  render_tree ~verbose tree |> Pretty.Svg.write_lines path
