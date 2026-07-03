module VarMap = Map.Make (Syntax.VarId)

type loc = Location.t

type object_info = {
  typ : Typ.t;
  size : int;
}

type frame = {
  locals : loc VarMap.t;
}

type t = {
  next_global_object_id : int;
  next_stack_object_id : int;
  next_heap_object_id : int;
  globals : loc VarMap.t;
  frames : frame list;
  objects : object_info Location.ObjectMap.t;
  store : Value.t Location.LocMap.t;
}

type error =
  | No_active_frame
  | Duplicate_variable of Syntax.varinfo
  | Unbound_variable of Syntax.varinfo
  | Unknown_object of Location.object_id
  | Invalid_location of loc
  | Uninitialized_read of loc
  | Invalid_object_size of int
  | Object_size_overflow of Typ.t
  | Unsupported_object_type of Typ.t
  | Unsupported_array_length of Typ.t

let ( let* ) = Result.bind

let empty =
  {
    next_global_object_id = 0;
    next_stack_object_id = 0;
    next_heap_object_id = 0;
    globals = VarMap.empty;
    frames = [];
    objects = Location.ObjectMap.empty;
    store = Location.LocMap.empty;
  }

(* Push an empty local-variable frame for a function call. *)
let enter_function mem =
  { mem with frames = { locals = VarMap.empty } :: mem.frames }

let valid_object_size size = size > 0

(* Compute the number of linear memory slots occupied by a CIL' type. *)
let rec object_size_of_type = function
  | Typ.TInt _ -> Ok 1
  | Typ.TPtr _ -> Ok 1
  | Typ.TArray (typ, Some len) ->
      let array_typ = Typ.TArray (typ, Some len) in
      if Int64.compare len 0L <= 0 then Error (Invalid_object_size 0)
      else
        let* elem_size = object_size_of_type typ in
        if Int64.compare len (Int64.of_int max_int) > 0 then
          Error (Object_size_overflow array_typ)
        else
          let len = Int64.to_int len in
          if elem_size > max_int / len then
            Error (Object_size_overflow array_typ)
          else Ok (elem_size * len)
  | Typ.TArray _ as typ -> Error (Unsupported_array_length typ)
  | (Typ.TVoid | Typ.TFun _) as typ -> Error (Unsupported_object_type typ)

(* Allocate a fresh stack object and return its base location. *)
let fresh_stack_object typ mem =
  let* size = object_size_of_type typ in
  if not (valid_object_size size) then Error (Invalid_object_size size)
  else
    let obj = Location.Stack mem.next_stack_object_id in
    let loc = { Location.obj; offset = 0 } in
    let info = { typ; size } in
    Ok
      ( loc,
        {
          mem with
          next_stack_object_id = mem.next_stack_object_id + 1;
          objects = Location.ObjectMap.add obj info mem.objects;
        } )

(* Remove an object, its metadata, and every stored value inside it. *)
let remove_object obj mem =
  let store =
    Location.LocMap.filter (fun loc _ -> loc.Location.obj <> obj) mem.store
  in
  { mem with objects = Location.ObjectMap.remove obj mem.objects; store }

(* Pop the current frame and deallocate all stack objects owned by it. *)
let leave_function mem =
  match mem.frames with
  | [] -> Error No_active_frame
  | frame :: frames ->
      let mem =
        VarMap.fold (fun _ loc mem -> remove_object loc.Location.obj mem)
          frame.locals mem
      in
      Ok { mem with frames }

(* Look up a varinfo binding in the current local frame only. *)
let find_local var = function
  | frame :: _ -> VarMap.find_opt var.Syntax.vid frame.locals
  | [] -> None

(* Look up a varinfo binding in the global-variable table. *)
let find_global var mem =
  VarMap.find_opt var.Syntax.vid mem.globals

(* Add a varinfo-to-location binding to a local frame. *)
let add_local_binding var loc frame =
  { locals = VarMap.add var.Syntax.vid loc frame.locals }

(* Bind a local varinfo to a fresh uninitialized stack object. *)
let allocate_local var mem =
  match mem.frames with
  | [] -> Error No_active_frame
  | frame :: frames -> (
      match VarMap.find_opt var.Syntax.vid frame.locals with
      | Some _ -> Error (Duplicate_variable var)
      | None ->
          let* loc, mem = fresh_stack_object var.Syntax.vtype mem in
          let frame = add_local_binding var loc frame in
          Ok (loc, { mem with frames = frame :: frames }) )

(* Bind a local varinfo to a fresh stack object initialized with value. *)
let bind_local var value mem =
  let* loc, mem = allocate_local var mem in
  Ok (loc, { mem with store = Location.LocMap.add loc value mem.store })

(* Resolve a varinfo through globals or the current frame according to vglob. *)
let loc_of_var var mem =
  let loc =
    if var.Syntax.vglob then find_global var mem
    else find_local var mem.frames
  in
  match loc with
  | Some loc -> Ok loc
  | None -> Error (Unbound_variable var)

(* Check that a location points inside an allocated object. *)
let check_location loc mem =
  match Location.ObjectMap.find_opt loc.Location.obj mem.objects with
  | None -> Error (Unknown_object loc.Location.obj)
  | Some info ->
      if 0 <= loc.Location.offset && loc.Location.offset < info.size then Ok ()
      else Error (Invalid_location loc)

(* Read the initialized value stored at a valid location. *)
let read loc mem =
  let* () = check_location loc mem in
  match Location.LocMap.find_opt loc mem.store with
  | Some value -> Ok value
  | None -> Error (Uninitialized_read loc)

(* Store a value at a valid location. *)
let write loc value mem =
  let* () = check_location loc mem in
  Ok { mem with store = Location.LocMap.add loc value mem.store }

let string_of_bindings locals =
  let bindings =
    VarMap.bindings locals
    |> List.map (fun (vid, loc) ->
           Printf.sprintf "#%d=%s" vid (Location.string_of_t loc))
  in
  "{" ^ String.concat ", " bindings ^ "}"

let string_of_frames frames =
  let frames =
    List.mapi
      (fun idx frame ->
        Printf.sprintf "frame%d%s" idx (string_of_bindings frame.locals))
      frames
  in
  "[" ^ String.concat "; " frames ^ "]"

let string_of_store store =
  let entries =
    Location.LocMap.bindings store
    |> List.map (fun (loc, value) ->
           Location.string_of_t loc ^ "=" ^ Value.string_of_t value)
  in
  "{" ^ String.concat ", " entries ^ "}"

let string_of_visible_values mem =
  match mem.frames with
  | [] -> "{}"
  | frame :: _ ->
      let entries =
        VarMap.bindings frame.locals
        |> List.map (fun (vid, loc) ->
               match Location.LocMap.find_opt loc mem.store with
               | Some value ->
                   Printf.sprintf "#%d |-> %s" vid (Value.string_of_t value)
               | None -> Printf.sprintf "#%d |-> ?" vid)
      in
      "{" ^ String.concat ", " entries ^ "}"

let string_of_t mem =
  string_of_visible_values mem

let string_of_error = function
  | No_active_frame -> "no active function frame"
  | Duplicate_variable var ->
      "duplicate variable: " ^ SyntaxUtil.string_of_var var
  | Unbound_variable var ->
      "unbound variable: " ^ SyntaxUtil.string_of_var var
  | Unknown_object obj ->
      "unknown memory object: " ^ Location.string_of_object_id obj
  | Invalid_location loc ->
      "invalid memory location: " ^ Location.string_of_t loc
  | Uninitialized_read loc ->
      "uninitialized read: " ^ Location.string_of_t loc
  | Invalid_object_size size ->
      Printf.sprintf "invalid object size: %d" size
  | Object_size_overflow typ ->
      "object size overflow: " ^ Typ.string_of_t typ
  | Unsupported_object_type typ ->
      "unsupported object type: " ^ Typ.string_of_t typ
  | Unsupported_array_length typ ->
      "unsupported array length: " ^ Typ.string_of_t typ
