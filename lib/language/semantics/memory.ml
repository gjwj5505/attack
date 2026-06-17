module IdMap = Map.Make (String)

module ObjectId = struct
  type t =
    | Global of int
    | Stack of int
    | Heap of int

  let compare = compare
end

module ObjectMap = Map.Make (ObjectId)

type object_id = ObjectId.t
type offset = int

type loc = {
  obj : object_id;
  offset : offset;
}

module Loc = struct
  type t = loc

  let compare = compare
end

module LocMap = Map.Make (Loc)

type object_info = {
  typ : Typ.t;
  size : int;
}

type frame = {
  locals : loc IdMap.t;
}

type t = {
  next_stack_object_id : int;
  next_heap_object_id : int;
  frames : frame list; (* 함수 호출 프레임 스택. 각 프레임은 변수 이름을 location에 연결한다. *)
  objects : object_info ObjectMap.t; (* 할당된 object의 타입과 크기 정보. location의 obj가 여기서 해석된다. *)
  store : Value.t LocMap.t; (* 실제 값 저장소. location이 가리키는 runtime value를 담는다. *)
}

type error =
  | No_active_frame
  | Duplicate_variable of Syntax.id
  | Unbound_variable of Syntax.id
  | Unknown_object of object_id
  | Invalid_dereference of loc
  | Invalid_object_size of int

let empty =
  {
    next_stack_object_id = 0;
    next_heap_object_id = 0;
    frames = [];
    objects = ObjectMap.empty;
    store = LocMap.empty;
  }

let enter_function mem =
  { mem with frames = { locals = IdMap.empty } :: mem.frames }

(* 현재 Typ.Int는 항상 size 1이다. 이 검사는 future array/struct layout 계산이
   잘못된 object size를 만들 때 잡기 위한 방어용이다. *)
let valid_object_size size = size > 0

let object_size_of_type = function
  | Typ.Int -> 1

let fresh_object typ mem =
  let size = object_size_of_type typ in
  if not (valid_object_size size) then Error (Invalid_object_size size)
  else
    let obj = ObjectId.Stack mem.next_stack_object_id in
    let info = { typ; size } in
    let loc = { obj; offset = 0 } in
    Ok
      ( loc,
        {
          mem with
          next_stack_object_id = mem.next_stack_object_id + 1;
          objects = ObjectMap.add obj info mem.objects;
        } )

let remove_object obj mem =
  let store =
    LocMap.filter (fun loc _ -> loc.obj <> obj) mem.store
  in
  { mem with objects = ObjectMap.remove obj mem.objects; store }

let leave_function mem =
  match mem.frames with
  | [] -> Error No_active_frame
  | frame :: frames ->
      let mem =
        IdMap.fold
          (fun _ loc mem -> remove_object loc.obj mem)
          frame.locals mem
      in
      Ok { mem with frames }

let find_local name = function
  (* C local lookup은 현재 함수 scope만 본다. Caller frame의 locals는 보이지 않는다. *)
  | frame :: _ -> IdMap.find_opt name frame.locals
  | [] -> None

let is_valid_deref_loc loc mem =
  match ObjectMap.find_opt loc.obj mem.objects with
  | None -> Error (Unknown_object loc.obj)
  | Some info ->
      if 0 <= loc.offset && loc.offset < info.size then Ok ()
      else Error (Invalid_dereference loc)

let declare ({ Syntax.typ; name } : Syntax.binding) value mem =
  match mem.frames with
  | [] -> Error No_active_frame
  | frame :: frames -> (
      match IdMap.find_opt name frame.locals with
      | Some _ -> Error (Duplicate_variable name)
      | None ->
          Result.bind (fresh_object typ mem) (fun (loc, mem) ->
              let store = LocMap.add loc value mem.store in
              let frame = { locals = IdMap.add name loc frame.locals } in
              Ok { mem with frames = frame :: frames; store }) )

let loc_of_lval lval mem =
  match lval with
  | Syntax.LVar name -> (
      match find_local name mem.frames with
      | Some loc -> Ok loc
      | None -> Error (Unbound_variable name) )

let read_lval lval mem =
  Result.bind (loc_of_lval lval mem) (fun loc ->
      Result.bind (is_valid_deref_loc loc mem) (fun () ->
          match LocMap.find_opt loc mem.store with
          | Some value -> Ok value
          | None ->
              (* 초기 subset에서는 모든 선언이 initializer를 가지므로 정상 memory라면
                 store lookup이 실패하지 않는다. 여기까지 오면 object bounds는 맞지만
                 store invariant가 깨진 상태다. *)
              Error (Invalid_dereference loc)))

let assign_lval lval value mem =
  Result.bind (loc_of_lval lval mem) (fun loc ->
      Result.bind (is_valid_deref_loc loc mem) (fun () ->
          Ok { mem with store = LocMap.add loc value mem.store }))

let string_of_object_id = function
  | ObjectId.Global id -> Printf.sprintf "global%d" id
  | ObjectId.Stack id -> Printf.sprintf "stack%d" id
  | ObjectId.Heap id -> Printf.sprintf "heap%d" id

let string_of_loc { obj; offset } =
  Printf.sprintf "%s+%d" (string_of_object_id obj) offset

let string_of_error = function
  | No_active_frame -> "no active function frame"
  | Duplicate_variable name -> "duplicate variable: " ^ name
  | Unbound_variable name -> "unbound variable: " ^ name
  | Unknown_object obj ->
      Printf.sprintf "unknown memory object: %s" (string_of_object_id obj)
  | Invalid_dereference loc ->
      "invalid memory dereference: " ^ string_of_loc loc
  | Invalid_object_size size ->
      Printf.sprintf "invalid object size: %d" size
