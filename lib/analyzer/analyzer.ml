(*
 * SNU 4190.664A Static Program Analysis
 * 2025 Jay Lee <jhlee@ropas.snu.ac.kr>, <jaeho.lee@snu.ac.kr>
 *)

open Language.Syntax

module Loc = Abs_domain.Loc
module Abs_val = Abs_domain.Abs_val
module Abs_mem = Abs_domain.Abs_mem
module Abs_sem = Abs_domain.Abs_sem

module EdgeSet = Set.Make (struct
  type t = Cmd.lbl * Cmd.lbl

  let compare = Stdlib.compare
end)

let rec terminal_edges (stmt : Cmd.lbl_t) (exit : Cmd.lbl) : EdgeSet.t =
  match stmt.cmd with
  | Cmd.Assign _ -> EdgeSet.singleton (stmt.lbl, exit)
  | Cmd.Seq (_, c2) -> terminal_edges c2 exit
  | Cmd.If (_, c1, c2) ->
      EdgeSet.union (terminal_edges c1 exit) (terminal_edges c2 exit)
  | Cmd.While (_, _) ->
      (* Exiting a while statement to its successor happens only on the false
         edge of the loop header. *)
      EdgeSet.singleton (stmt.lbl, exit)

let rec collect_widen_edges (stmt : Cmd.lbl_t) : EdgeSet.t =
  match stmt.cmd with
  | Cmd.Assign _ -> EdgeSet.empty
  | Cmd.Seq (c1, c2) ->
      EdgeSet.union (collect_widen_edges c1) (collect_widen_edges c2)
  | Cmd.If (_, c1, c2) ->
      EdgeSet.union (collect_widen_edges c1) (collect_widen_edges c2)
  | Cmd.While (_, body) ->
      EdgeSet.union (terminal_edges body stmt.lbl) (collect_widen_edges body)

let analysis (prog : Cmd.lbl_t) : Abs_mem.t =
  let prog = Cmd.relabel prog in
  let table = Cmd.tabulate prog in
  let widen_edges = collect_widen_edges prog in
  let start = 1 in
  let exit = 99 in
  let Cfg.{ next; next_true; next_false } = Cfg.make prog exit in

  let wl = Queue.create () in
  let sem = ref (Cmd.Lbl_map.map (fun _ -> Abs_mem.Bot) table) in
  sem := Cmd.Lbl_map.add start Abs_mem.empty !sem;
  sem := Cmd.Lbl_map.add exit Abs_mem.Bot !sem;

  Queue.push start wl;

  let rec run () =
    if Queue.is_empty wl then ()
    else
      let cur = Queue.pop wl in
      (* print_endline (Abs_sem.string_of_t !sem); *)
      (* print_endline ("Processing label: " ^ Cmd.Lbl_map.string_of_key cur); *)
      if cur = exit then run () (* skip processing the exit label *)
      else
        let cur_mem = Cmd.Lbl_map.find cur !sem in
        let update_list =
          match Cmd.Lbl_map.find cur table with
          | Cmd.Assign (x, e) ->
              let v = Eval.antp_exp cur_mem e in
              [ (next cur, Abs_mem.add x v cur_mem) ]
          | Cmd.If (e, _, _) | Cmd.While (e, _) ->
              [
                (next_true cur, Filter.filter_t e cur_mem);
                (next_false cur, Filter.filter_f e cur_mem);
              ]
          | _ -> [ (next cur, cur_mem) ]
        in
        List.iter
          (fun (nex, mem) ->
            let old_mem = Cmd.Lbl_map.find nex !sem in
            let new_mem =
              if EdgeSet.mem (cur, nex) widen_edges then
                Abs_mem.widen old_mem mem
              else Abs_mem.join old_mem mem
            in
            if not (Abs_mem.leq new_mem old_mem) then (
              sem := Cmd.Lbl_map.add nex new_mem !sem;
              Queue.push nex wl))
          update_list;
        run ()
  in
  run ();
  (* print_endline (Abs_sem.string_of_t !sem); *)
  !sem |> Cmd.Lbl_map.find exit
