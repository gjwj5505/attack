open HoleSyntax

module HoleIdMap = Map.Make (struct
  type t = hole_id

  let compare = Int.compare
end)

module HoleIdSet = Set.Make (struct
  type t = hole_id

  let compare = Int.compare
end)

(** A substitution is kept normalized and idempotent.

    The domains of [exps] and [stmt_seqs] must be disjoint because one hole ID
    has exactly one sort within a proof component. *)
type t = {
  exps : exp HoleIdMap.t;
  stmt_seqs : stmt_seq_item list HoleIdMap.t;
}

type hole_ids = {
  exp_ids : HoleIdSet.t;
  stmt_seq_ids : HoleIdSet.t;
}

type hole_sort =
  | Exp
  | StmtSeq

type error =
  | Already_bound of hole_id
  | Inconsistent_domains of hole_id (* 한 hold_id가 동시에 exp, stmt_seq에 bind됨 *)
  | Sort_mismatch of {
      hole : hole_id;
      expected : hole_sort;
      actual : hole_sort;
    }
  | Occurs_check_failed of hole_id

type invariant_error =
  | Invalid_hole_id of hole_id
  | Overlapping_domains of hole_id
  | Inconsistent_hole_sort of hole_id
  | Non_idempotent of {
      hole : hole_id;
      sort : hole_sort;
    }

let empty =
  {
    exps = HoleIdMap.empty;
    stmt_seqs = HoleIdMap.empty;
  }

let find_exp hole substitution = HoleIdMap.find_opt hole substitution.exps

let find_stmt_seq hole substitution =
  HoleIdMap.find_opt hole substitution.stmt_seqs

let rec apply_exp substitution = function
  | ExpHole hole -> (
      match find_exp hole substitution with
      | Some exp -> exp
      | None -> ExpHole hole)
  | Const _ as exp -> exp
  | Lval lval -> Lval (apply_lval substitution lval)
  | UnOp (op, exp, typ) -> UnOp (op, apply_exp substitution exp, typ)
  | BinOp (op, left, right, typ) ->
      BinOp
        ( op,
          apply_exp substitution left,
          apply_exp substitution right,
          typ )
  | AddrOf lval -> AddrOf (apply_lval substitution lval)
  | StartOf lval -> StartOf (apply_lval substitution lval)

and apply_lval substitution (host, offset) =
  (apply_lhost substitution host, apply_offset substitution offset)

and apply_lhost substitution = function
  | Var _ as host -> host
  | Mem exp -> Mem (apply_exp substitution exp)

and apply_offset substitution = function
  | NoOffset -> NoOffset
  | Field (field, offset) -> Field (field, apply_offset substitution offset)
  | Index (exp, offset) ->
      Index (apply_exp substitution exp, apply_offset substitution offset)

let apply_instr substitution = function
  | Set (lval, exp) ->
      Set (apply_lval substitution lval, apply_exp substitution exp)
  | Call (return, callee, arguments) ->
      Call
        ( Option.map (apply_lval substitution) return,
          apply_exp substitution callee,
          List.map (apply_exp substitution) arguments )

let rec apply_stmt substitution stmt =
  { stmt with skind = apply_stmtkind substitution stmt.skind }

and apply_stmtkind substitution = function
  | Instr instrs -> Instr (List.map (apply_instr substitution) instrs)
  | Return exp -> Return (Option.map (apply_exp substitution) exp)
  | If (condition, then_block, else_block) ->
      If
        ( apply_exp substitution condition,
          apply_block substitution then_block,
          apply_block substitution else_block )
  | Loop block -> Loop (apply_block substitution block)
  | Break -> Break
  | Continue -> Continue
  | Block block -> Block (apply_block substitution block)

and apply_block substitution block =
  { bstmts = apply_stmt_seq substitution block.bstmts }

and apply_stmt_seq substitution = function
  | [] -> []
  | Stmt stmt :: rest ->
      Stmt (apply_stmt substitution stmt)
      :: apply_stmt_seq substitution rest
  | [ StmtSeqHole hole ] -> (
      match find_stmt_seq hole substitution with
      | Some replacement -> replacement
      | None -> [ StmtSeqHole hole ])
  | StmtSeqHole hole :: _ ->
      invalid_arg
        (Printf.sprintf
           "HoleSubstitution.apply_stmt_seq: hole H%d is not final"
           hole)

let apply_fundec substitution fundec =
  { fundec with sbody = apply_block substitution fundec.sbody }

let rec apply_init substitution = function
  | SingleInit exp -> SingleInit (apply_exp substitution exp)
  | CompoundInit (typ, fields) ->
      CompoundInit
        ( typ,
          List.map
            (fun (offset, init) ->
              (apply_offset substitution offset, apply_init substitution init))
            fields )

let apply_initinfo substitution initinfo =
  { init = Option.map (apply_init substitution) initinfo.init }

let apply_global substitution = function
  | GFun fundec -> GFun (apply_fundec substitution fundec)
  | GVarDecl _ as global -> global
  | GVar (var, initinfo) ->
      GVar (var, apply_initinfo substitution initinfo)

let apply_file substitution file =
  {
    file with
    globals = List.map (apply_global substitution) file.globals;
  }

let apply_ast substitution = function
  | AExp exp -> AExp (apply_exp substitution exp)
  | ALval lval -> ALval (apply_lval substitution lval)
  | AOffset offset -> AOffset (apply_offset substitution offset)
  | AInstr instr -> AInstr (apply_instr substitution instr)
  | AStmt stmt -> AStmt (apply_stmt substitution stmt)
  | ABlock block -> ABlock (apply_block substitution block)
  | AFundec fundec -> AFundec (apply_fundec substitution fundec)
  | AInit init -> AInit (apply_init substitution init)
  | AGlobal global -> AGlobal (apply_global substitution global)
  | AFile file -> AFile (apply_file substitution file)

let rec occurs_exp hole = function
  | ExpHole other -> Int.equal hole other
  | Const _ -> false
  | Lval lval -> occurs_lval hole lval
  | UnOp (_, exp, _) -> occurs_exp hole exp
  | BinOp (_, left, right, _) ->
      occurs_exp hole left || occurs_exp hole right
  | AddrOf lval | StartOf lval -> occurs_lval hole lval

and occurs_lval hole (host, offset) =
  occurs_lhost hole host || occurs_offset hole offset

and occurs_lhost hole = function
  | Var _ -> false
  | Mem exp -> occurs_exp hole exp

and occurs_offset hole = function
  | NoOffset -> false
  | Field (_, offset) -> occurs_offset hole offset
  | Index (exp, offset) ->
      occurs_exp hole exp || occurs_offset hole offset

let rec occurs_stmt_seq hole = function
  | [] -> false
  | Stmt stmt :: rest ->
      occurs_stmt_seq_in_stmt hole stmt || occurs_stmt_seq hole rest
  | StmtSeqHole other :: rest ->
      Int.equal hole other || occurs_stmt_seq hole rest

and occurs_stmt_seq_in_stmt hole stmt =
  occurs_stmt_seq_in_stmtkind hole stmt.skind

and occurs_stmt_seq_in_stmtkind hole = function
  | Instr _ | Return _ | Break | Continue -> false
  | If (_, then_block, else_block) ->
      occurs_stmt_seq_in_block hole then_block
      || occurs_stmt_seq_in_block hole else_block
  | Loop block | Block block -> occurs_stmt_seq_in_block hole block

and occurs_stmt_seq_in_block hole block =
  occurs_stmt_seq hole block.bstmts

let bind_exp substitution hole rhs =
  match (find_exp hole substitution, find_stmt_seq hole substitution) with
  | Some _, Some _ -> Error (Inconsistent_domains hole)
  | Some _, None -> Error (Already_bound hole)
  | None, Some _ ->
      Error
        (Sort_mismatch { hole; expected = Exp; actual = StmtSeq })
  | None, None ->
      let rhs = apply_exp substitution rhs in
      if occurs_exp hole rhs then Error (Occurs_check_failed hole)
      else
        let binding =
          { empty with exps = HoleIdMap.singleton hole rhs }
        in
        let exps =
          substitution.exps
          |> HoleIdMap.map (apply_exp binding)
          |> HoleIdMap.add hole rhs
        in
        let stmt_seqs =
          HoleIdMap.map (apply_stmt_seq binding) substitution.stmt_seqs
        in
        Ok { exps; stmt_seqs }

let bind_stmt_seq substitution hole rhs =
  match (find_stmt_seq hole substitution, find_exp hole substitution) with
  | Some _, Some _ -> Error (Inconsistent_domains hole)
  | Some _, None -> Error (Already_bound hole)
  | None, Some _ ->
      Error
        (Sort_mismatch { hole; expected = StmtSeq; actual = Exp })
  | None, None ->
      let rhs = apply_stmt_seq substitution rhs in
      if occurs_stmt_seq hole rhs then Error (Occurs_check_failed hole)
      else
        let binding =
          { empty with stmt_seqs = HoleIdMap.singleton hole rhs }
        in
        let stmt_seqs =
          substitution.stmt_seqs
          |> HoleIdMap.map (apply_stmt_seq binding)
          |> HoleIdMap.add hole rhs
        in
        Ok { exps = substitution.exps; stmt_seqs }

let fold_bind bind bindings substitution =
  HoleIdMap.fold
    (fun hole rhs result ->
      match result with
      | Error _ -> result
      | Ok substitution -> bind substitution hole rhs)
    bindings (Ok substitution)

(** [compose ~after ~before] applies [before] first and [after] second.
    [after] must be an idempotent delta produced under [before]. *)
(* after에서 하나씩 떼서 before에다가 먹임 *)
let compose ~after ~before =
  match fold_bind bind_exp after.exps before with
  | Error _ as error -> error
  | Ok substitution ->
      fold_bind bind_stmt_seq after.stmt_seqs substitution

let no_hole_ids =
  {
    exp_ids = HoleIdSet.empty;
    stmt_seq_ids = HoleIdSet.empty;
  }

let union_hole_ids left right =
  {
    exp_ids = HoleIdSet.union left.exp_ids right.exp_ids;
    stmt_seq_ids =
      HoleIdSet.union left.stmt_seq_ids right.stmt_seq_ids;
  }

let holes_in_list holes_in items =
  List.fold_left
    (fun holes item -> union_hole_ids holes (holes_in item))
    no_hole_ids items

let holes_in_option holes_in = function
  | None -> no_hole_ids
  | Some item -> holes_in item

let rec holes_in_exp = function
  | ExpHole hole ->
      { no_hole_ids with exp_ids = HoleIdSet.singleton hole }
  | Const _ -> no_hole_ids
  | Lval lval | AddrOf lval | StartOf lval -> holes_in_lval lval
  | UnOp (_, exp, _) -> holes_in_exp exp
  | BinOp (_, left, right, _) ->
      union_hole_ids (holes_in_exp left) (holes_in_exp right)

and holes_in_lval (host, offset) =
  union_hole_ids (holes_in_lhost host) (holes_in_offset offset)

and holes_in_lhost = function
  | Var _ -> no_hole_ids
  | Mem exp -> holes_in_exp exp

and holes_in_offset = function
  | NoOffset -> no_hole_ids
  | Field (_, offset) -> holes_in_offset offset
  | Index (exp, offset) ->
      union_hole_ids (holes_in_exp exp) (holes_in_offset offset)

let holes_in_instr = function
  | Set (lval, exp) ->
      union_hole_ids (holes_in_lval lval) (holes_in_exp exp)
  | Call (return, callee, arguments) ->
      union_hole_ids
        (holes_in_option holes_in_lval return)
        (union_hole_ids
           (holes_in_exp callee)
           (holes_in_list holes_in_exp arguments))

let rec holes_in_stmt stmt = holes_in_stmtkind stmt.skind

and holes_in_stmtkind = function
  | Instr instrs -> holes_in_list holes_in_instr instrs
  | Return exp -> holes_in_option holes_in_exp exp
  | If (condition, then_block, else_block) ->
      union_hole_ids
        (holes_in_exp condition)
        (union_hole_ids
           (holes_in_block then_block)
           (holes_in_block else_block))
  | Loop block | Block block -> holes_in_block block
  | Break | Continue -> no_hole_ids

and holes_in_block block = holes_in_stmt_seq block.bstmts

and holes_in_stmt_seq items =
  List.fold_left
    (fun holes -> function
      | Stmt stmt -> union_hole_ids holes (holes_in_stmt stmt)
      | StmtSeqHole hole ->
          {
            holes with
            stmt_seq_ids = HoleIdSet.add hole holes.stmt_seq_ids;
          })
    no_hole_ids items

let domain_ids bindings =
  HoleIdMap.fold
    (fun hole _ holes -> HoleIdSet.add hole holes)
    bindings HoleIdSet.empty

let holes_in_ranges substitution =
  let holes =
    HoleIdMap.fold
      (fun _ rhs holes -> union_hole_ids holes (holes_in_exp rhs))
      substitution.exps no_hole_ids
  in
  HoleIdMap.fold
    (fun _ rhs holes -> union_hole_ids holes (holes_in_stmt_seq rhs))
    substitution.stmt_seqs holes

let first_hole holes =
  if HoleIdSet.is_empty holes then None
  else Some (HoleIdSet.min_elt holes)

let first_common_hole left right =
  first_hole (HoleIdSet.inter left right)

(** Checks substitution-specific invariants. Structural validity of each
    right-hand-side syntax value remains [HoleSyntaxChecker]'s responsibility. *)
let check_well_formed substitution =
  let exp_domain = domain_ids substitution.exps in
  let stmt_seq_domain = domain_ids substitution.stmt_seqs in
  let range_holes = holes_in_ranges substitution in
  let all_exp_ids =
    HoleIdSet.union exp_domain range_holes.exp_ids
  in
  let all_stmt_seq_ids =
    HoleIdSet.union stmt_seq_domain range_holes.stmt_seq_ids
  in
  let all_ids = HoleIdSet.union all_exp_ids all_stmt_seq_ids in
  match first_hole all_ids with
  | Some hole when hole <= 0 -> Error (Invalid_hole_id hole)
  | _ -> (
      match first_common_hole exp_domain stmt_seq_domain with
      | Some hole -> Error (Overlapping_domains hole)
      | None -> (
          match first_common_hole all_exp_ids all_stmt_seq_ids with
          | Some hole -> Error (Inconsistent_hole_sort hole)
          | None -> (
              match first_common_hole exp_domain range_holes.exp_ids with
              | Some hole -> Error (Non_idempotent { hole; sort = Exp })
              | None -> (
                  match
                    first_common_hole stmt_seq_domain
                      range_holes.stmt_seq_ids
                  with
                  | Some hole ->
                      Error (Non_idempotent { hole; sort = StmtSeq })
                  | None -> Ok () ) ) ) )

let string_of_hole_sort = function
  | Exp -> "expression"
  | StmtSeq -> "statement sequence"

let string_of_error = function
  | Already_bound hole -> Printf.sprintf "hole H%d is already bound" hole
  | Inconsistent_domains hole ->
      Printf.sprintf
        "hole H%d occurs in both substitution domains" hole
  | Sort_mismatch { hole; expected; actual } ->
      Printf.sprintf "hole H%d has sort %s, but sort %s was expected" hole
        (string_of_hole_sort actual)
        (string_of_hole_sort expected)
  | Occurs_check_failed hole ->
      Printf.sprintf "occurs check failed for hole H%d" hole

let string_of_invariant_error = function
  | Invalid_hole_id hole ->
      Printf.sprintf "invalid hole ID H%d: expected a positive integer" hole
  | Overlapping_domains hole ->
      Printf.sprintf
        "hole H%d occurs in both substitution domains" hole
  | Inconsistent_hole_sort hole ->
      Printf.sprintf
        "hole H%d occurs as both an expression and a statement-sequence hole"
        hole
  | Non_idempotent { hole; sort } ->
      Printf.sprintf
        "bound %s hole H%d still occurs in the substitution range"
        (string_of_hole_sort sort) hole

let string_of_stmt_seq items =
  items
  |> List.map (string_of_stmt_seq_item ~lvl:0)
  |> String.concat " "
  |> Printf.sprintf "[%s]"

let string_of_bindings string_of_rhs bindings =
  bindings
  |> HoleIdMap.bindings
  |> List.map (fun (hole, rhs) ->
         Printf.sprintf "H%d -> %s" hole (string_of_rhs rhs))
  |> String.concat "; "

let string_of_t substitution =
  Printf.sprintf "{ exps = [%s]; stmt_seqs = [%s] }"
    (string_of_bindings Exp.string_of_t substitution.exps)
    (string_of_bindings string_of_stmt_seq substitution.stmt_seqs)
