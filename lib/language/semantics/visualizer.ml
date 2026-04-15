open BigStep
open Syntax
open Size

(* --- 데이터 구조 정의 --- *)
type box = { lines: string list; width: int; height: int }
type side = Top | Bottom

(* --- 박스 생성 및 정렬 유틸리티 --- *)

let make_box s = 
  (* 앞뒤에 생기는 불필요한 빈 줄(\n) 제거 로직 *)
  let raw_lines = String.split_on_char '\n' s in
  let rec trim_empty = function
    | "" :: tl -> trim_empty tl
    | lines -> lines
  in
  let lines = 
    raw_lines 
    |> trim_empty           (* 앞쪽 빈 줄 제거 *)
    |> List.rev |> trim_empty |> List.rev (* 뒤쪽 빈 줄 제거 *)
  in
  (* 모든 줄이 비어버린 경우 최소 한 줄 유지 *)
  let lines = if lines = [] then [""] else lines in
  let width = List.fold_left (fun acc l -> max acc (String.length l)) 0 lines in
  { lines; width; height = List.length lines }

let empty_box = { lines = []; width = 0; height = 0 }

let s_env e = "{" ^ (Environment.string_of_env e) ^ "}"

let pad side b target_h =
  let diff = target_h - b.height in
  if diff <= 0 then b.lines
  else
    let padding = List.init diff (fun _ -> String.make b.width ' ') in
    match side with
    | Top -> b.lines @ padding
    | Bottom -> padding @ b.lines

(* --- 레이아웃 엔진 핵심 --- *)

let make_conclusion env_obj cmd_str res_str =
  let b_env = make_box (s_env env_obj) in
  let b_turn = make_box "|-" in
  let b_cmd = make_box cmd_str in
  let b_arrow = make_box "=>" in
  let b_res = make_box res_str in
  
  let boxes = [b_env; b_turn; b_cmd; b_arrow; b_res] in
  let max_h = List.fold_left (fun acc b -> max acc b.height) 0 boxes in
  
  (* 각 박스를 상단 정렬(Top)하고, 여러 줄일 경우 너비 패딩을 채워 간격을 일정하게 유지 *)
  let adjusted_boxes = [
    { b_env with lines = List.map (fun s -> (String.make (b_env.width - String.length s) ' ') ^ s) (pad Top b_env max_h) };
    { b_turn with lines = pad Top b_turn max_h };
    { b_cmd with lines = List.map (fun s -> s ^ (String.make (b_cmd.width - String.length s) ' ')) (pad Top b_cmd max_h) };
    { b_arrow with lines = pad Top b_arrow max_h };
    { b_res with lines = pad Top b_res max_h }
  ] in
  
  (* 모든 요소를 한 칸(" ") 간격으로 결합 *)
  let combined_lines = List.init max_h (fun i ->
    String.concat " " (List.map (fun b -> List.nth b.lines i) adjusted_boxes)
  ) in
  
  let total_w = List.fold_left (fun acc b -> acc + b.width) 0 adjusted_boxes + (List.length adjusted_boxes - 1) in
  { lines = combined_lines; width = total_w; height = max_h }

let build_proof rule_name size premises conclusion_box =
  let gap = 3 in
  let premise_box = match premises with
    | [] -> empty_box
    | [p] -> p
    | ps -> 
        let max_ph = List.fold_left (fun acc b -> max acc b.height) 0 ps in
        let padded_ps = List.map (fun b -> { b with lines = pad Bottom b max_ph; height = max_ph }) ps in
        List.fold_left (fun acc b -> 
          let combined = List.map2 (fun s1 s2 -> s1 ^ (String.make gap ' ') ^ s2) acc.lines b.lines in
          { lines = combined; width = acc.width + gap + b.width; height = max_ph }
        ) (List.hd padded_ps) (List.tl padded_ps)
  in

  let rule_label = Printf.sprintf "[%s | prog=%d | proof=%d] " rule_name size.prog_size size.proof_size in
  let b_label = make_box rule_label in
  let full_h = max b_label.height conclusion_box.height in
  
  let l_label = pad Top b_label full_h in
  let l_conc = pad Top conclusion_box full_h in
  
  let full_conc_lines = List.map2 (fun s1 s2 -> s1 ^ s2) l_label l_conc in
  let full_conc_w = b_label.width + conclusion_box.width in
  
  let max_w = max premise_box.width full_conc_w in
  let line = String.make max_w '-' in
  
  let center_lines b w =
    if b.width = 0 && b.height = 0 then []
    else
      let left_pad = (w - b.width) / 2 in
      let right_pad = w - b.width - left_pad in
      List.map (fun s -> (String.make left_pad ' ') ^ s ^ (String.make right_pad ' ')) b.lines
  in
  
  let p_lines = center_lines premise_box max_w in
  let c_lines = center_lines {lines=full_conc_lines; width=full_conc_w; height=full_h} max_w in
  
  { lines = p_lines @ [line] @ c_lines;
    width = max_w; height = List.length p_lines + 1 + List.length c_lines }

(* --- 구문 트리 순회 (AST -> Box) --- *)

let rec box_of_etree t =
  match t with
  | EInt (_, (env, e, v)) -> 
      build_proof "E-Int" (sizeof_etree t) [] (make_conclusion env (Exp.string_of_t e) (string_of_int v))
  | EVar (_, (env, e, v)) -> 
      build_proof "E-Var" (sizeof_etree t) [] (make_conclusion env (Exp.string_of_t e) (string_of_int v))
  | EBop ((t1, t2), (env, e, v)) -> 
      build_proof "E-Bop" (sizeof_etree t) [box_of_etree t1; box_of_etree t2] (make_conclusion env (Exp.string_of_t e) (string_of_int v))
  | EUop (t1, (env, e, v)) -> 
      build_proof "E-Uop" (sizeof_etree t) [box_of_etree t1] (make_conclusion env (Exp.string_of_t e) (string_of_int v))

let rec box_of_ctree t =
  match t with
  | CAssign (et, (env, c, env')) -> 
      build_proof "S-Assign" (sizeof_ctree t) [box_of_etree et] (make_conclusion env (Cmd.string_of_t c) (s_env env'))
  | CSeq ((t1, t2), (env, c, env')) -> 
      build_proof "S-Seq" (sizeof_ctree t) [box_of_ctree t1; box_of_ctree t2] (make_conclusion env (Cmd.string_of_t c) (s_env env'))
  | CIfTrue ((et, ct), (env, c, env')) -> 
      build_proof "S-IfTrue" (sizeof_ctree t) [box_of_etree et; box_of_ctree ct] (make_conclusion env (Cmd.string_of_t c) (s_env env'))
  | CIfFalse ((et, ct), (env, c, env')) -> 
      build_proof "S-IfFalse" (sizeof_ctree t) [box_of_etree et; box_of_ctree ct] (make_conclusion env (Cmd.string_of_t c) (s_env env'))
  | CWhileTrue ((et, t_body, t_rest), (env, c, env')) -> 
      build_proof "S-WhileTrue" (sizeof_ctree t) [box_of_etree et; box_of_ctree t_body; box_of_ctree t_rest] (make_conclusion env (Cmd.string_of_t c) (s_env env'))
  | CWhileFalse (et, (env, c, env')) -> 
      build_proof "S-WhileFalse" (sizeof_ctree t) [box_of_etree et] (make_conclusion env (Cmd.string_of_t c) (s_env env'))


let print_tree tree =
  let final_box = match tree with 
    | ETree t -> box_of_etree t 
    | CTree t -> box_of_ctree t 
  in
  List.iter print_endline final_box.lines

(* TODO: 코드가 두 줄 이상일 경우 공백 3칸되는 문제(box)로 관리해서 그런듯, 결과 env가 위로 올라가있는 문제 *)
