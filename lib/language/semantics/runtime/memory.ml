module VarMap = Map.Make (Syntax.VarId)

type loc = Location.t

type object_info = {
  typ : Typ.t;
  size : int;
}

type frame = {
  locals : loc VarMap.t;
}

type storage = {
  next_object_id : int;
  objects : object_info Location.ObjectMap.t;
  store : Value.t Location.LocMap.t;
}

type stack_state = {
  frame : frame;
  storage : storage;
}

type global_state = {
  bindings : loc VarMap.t;
  storage : storage;
}

type t = {
  stack : stack_state option;
  global : global_state;
  heap : storage;
}

type storage_area =
  | Stack_area
  | Global_area
  | Heap_area

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
  | Invalid_next_object_id of {
      area : storage_area;
      next_object_id : int;
    }
  | Invalid_object_area of {
      expected : storage_area;
      object_id : Location.object_id;
    }
  | Invalid_object_id of {
      object_id : Location.object_id;
      next_object_id : int;
    }
  | Object_size_mismatch of {
      object_id : Location.object_id;
      expected : int;
      actual : int;
    }
  | Invalid_binding_scope of {
      variable : Syntax.VarId.t;
      expected : Syntax.VarId.scope;
    }
  | Invalid_binding_location of {
      variable : Syntax.VarId.t;
      location : loc;
    }
  | Duplicate_binding_location of loc
  | Invalid_stored_location of loc
  | Stored_value_type_mismatch of {
      location : loc;
      typ : Typ.t;
      value : Value.t;
    }

let ( let* ) = Result.bind

let empty_storage =
  {
    next_object_id = 0;
    objects = Location.ObjectMap.empty;
    store = Location.LocMap.empty;
  }

let empty_stack =
  { frame = { locals = VarMap.empty }; storage = empty_storage }

let empty_global =
  { bindings = VarMap.empty; storage = empty_storage }

let empty =
  { stack = None; global = empty_global; heap = empty_storage }

(* Replace the active stack state with an empty callee stack. *)
let enter_function mem =
  { mem with stack = Some empty_stack }

let valid_object_size size = size > 0

(* Compute the number of linear memory slots occupied by a CIL-- type. *)
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

let area_of_object = function
  | Location.Stack _ -> Stack_area
  | Location.Global _ -> Global_area
  | Location.Heap _ -> Heap_area

let id_of_object = function
  | Location.Stack id | Location.Global id | Location.Heap id -> id

let active_object_size = function
  | Typ.TInt Typ.IInt -> Ok 1
  | typ -> Error (Unsupported_object_type typ)

let check_object area storage (object_id, info) =
  if area_of_object object_id <> area then
    Error (Invalid_object_area { expected = area; object_id })
  else
    let id = id_of_object object_id in
    if id < 0 || id >= storage.next_object_id then
      Error
        (Invalid_object_id
           { object_id; next_object_id = storage.next_object_id })
    else
      let* expected = active_object_size info.typ in
      if info.size = expected then Ok ()
      else
        Error
          (Object_size_mismatch
             { object_id; expected; actual = info.size })

let check_stored_value area storage (location, value) =
  if area_of_object location.Location.obj <> area then
    Error
      (Invalid_object_area
         { expected = area; object_id = location.Location.obj })
  else
    match Location.ObjectMap.find_opt location.Location.obj storage.objects with
    | None -> Error (Invalid_stored_location location)
    | Some info ->
        if location.offset < 0 || location.offset >= info.size then
          Error (Invalid_stored_location location)
        else
          match info.typ, value with
          | Typ.TInt Typ.IInt, Value.Int { ikind = Typ.IInt; _ } -> Ok ()
          | _ ->
              Error
                (Stored_value_type_mismatch
                   { location; typ = info.typ; value })

let rec check_items check = function
  | [] -> Ok ()
  | item :: items ->
      let* () = check item in
      check_items check items

let check_storage area storage =
  if storage.next_object_id < 0 then
    Error
      (Invalid_next_object_id
         { area; next_object_id = storage.next_object_id })
  else
    let* () =
      check_items (check_object area storage)
        (Location.ObjectMap.bindings storage.objects)
    in
    check_items (check_stored_value area storage)
      (Location.LocMap.bindings storage.store)

let check_bindings ~area ~expected_scope storage bindings =
  let rec loop used_locations = function
    | [] -> Ok ()
    | (variable, location) :: bindings ->
        if Syntax.VarId.scope variable <> expected_scope then
          Error (Invalid_binding_scope { variable; expected = expected_scope })
        else if
          area_of_object location.Location.obj <> area
          || location.offset <> 0
          || not
               (Location.ObjectMap.mem location.Location.obj storage.objects)
        then Error (Invalid_binding_location { variable; location })
        else if Location.LocSet.mem location used_locations then
          Error (Duplicate_binding_location location)
        else
          loop (Location.LocSet.add location used_locations) bindings
  in
  loop Location.LocSet.empty (VarMap.bindings bindings)

let check_stack_bindings storage bindings =
  match VarMap.bindings bindings with
  | [] -> Ok ()
  | (variable, _) :: _ -> (
      match Syntax.VarId.scope variable with
      | Syntax.VarId.Global ->
          Error
            (Invalid_binding_scope
               {
                 variable;
                 expected = Syntax.VarId.Function "<active function>";
               })
      | Syntax.VarId.Function function_name ->
          check_bindings ~area:Stack_area
            ~expected_scope:(Syntax.VarId.Function function_name)
            storage bindings )

let check_well_formed mem =
  let* () = check_storage Global_area mem.global.storage in
  let* () =
    check_bindings ~area:Global_area ~expected_scope:Syntax.VarId.Global
      mem.global.storage mem.global.bindings
  in
  let* () = check_storage Heap_area mem.heap in
  match mem.stack with
  | None -> Ok ()
  | Some stack ->
      let* () = check_storage Stack_area stack.storage in
      check_stack_bindings stack.storage stack.frame.locals

(* Allocate a fresh object in the active stack storage. *)
let fresh_stack_object typ (stack : stack_state) =
  let* size = object_size_of_type typ in
  if not (valid_object_size size) then Error (Invalid_object_size size)
  else
    let storage = stack.storage in
    let obj = Location.Stack storage.next_object_id in
    let loc = { Location.obj; offset = 0 } in
    let info = { typ; size } in
    Ok
      ( loc,
        {
          stack with
          storage =
            {
              storage with
              next_object_id = storage.next_object_id + 1;
              objects = Location.ObjectMap.add obj info storage.objects;
            };
        } )

(* Restore the caller stack while retaining the current global and heap state. *)
let leave_function ~caller_stack mem =
  match mem.stack with
  | None -> Error No_active_frame
  | Some _ -> Ok { mem with stack = caller_stack }

(* Look up a varinfo binding in the current local frame only. *)
let find_local var = function
  | Some stack -> VarMap.find_opt var.Syntax.vid stack.frame.locals
  | None -> None

(* Look up a varinfo binding in the global-variable table. *)
let find_global var mem =
  VarMap.find_opt var.Syntax.vid mem.global.bindings

(* Add a varinfo-to-location binding to a local frame. *)
let add_local_binding var loc frame =
  { locals = VarMap.add var.Syntax.vid loc frame.locals }

(* Bind a local varinfo to a fresh uninitialized stack object. *)
let allocate_local var mem =
  match mem.stack with
  | None -> Error No_active_frame
  | Some stack -> (
      match VarMap.find_opt var.Syntax.vid stack.frame.locals with
      | Some _ -> Error (Duplicate_variable var)
      | None ->
          let* loc, stack = fresh_stack_object var.Syntax.vtype stack in
          let frame = add_local_binding var loc stack.frame in
          Ok (loc, { mem with stack = Some { stack with frame } }) )

(* Bind a local varinfo to a fresh stack object initialized with value. *)
let bind_local var value mem =
  let* loc, mem = allocate_local var mem in
  match mem.stack with
  | None -> Error No_active_frame
  | Some stack ->
      let storage = stack.storage in
      let storage =
        { storage with store = Location.LocMap.add loc value storage.store }
      in
      Ok (loc, { mem with stack = Some { stack with storage } })

(* Resolve a varinfo through globals or the current frame according to vglob. *)
let loc_of_var var mem =
  let loc =
    if var.Syntax.vglob then find_global var mem
    else find_local var mem.stack
  in
  match loc with
  | Some loc -> Ok loc
  | None -> Error (Unbound_variable var)

let storage_for_object obj mem =
  match obj with
  | Location.Stack _ ->
      Option.map (fun (stack : stack_state) -> stack.storage) mem.stack
  | Location.Global _ -> Some mem.global.storage
  | Location.Heap _ -> Some mem.heap

(* Check that a location points inside an allocated object. *)
let check_location loc mem =
  let info =
    match storage_for_object loc.Location.obj mem with
    | None -> None
    | Some storage ->
        Location.ObjectMap.find_opt loc.Location.obj storage.objects
  in
  match info with
  | None -> Error (Unknown_object loc.Location.obj)
  | Some info ->
      if 0 <= loc.Location.offset && loc.Location.offset < info.size then Ok ()
      else Error (Invalid_location loc)

(* Read the initialized value stored at a valid location. *)
let read loc mem =
  let* () = check_location loc mem in
  let value =
    match storage_for_object loc.Location.obj mem with
    | None -> None
    | Some storage -> Location.LocMap.find_opt loc storage.store
  in
  match value with
  | Some value -> Ok value
  | None -> Error (Uninitialized_read loc)

(* Store a value at a valid location. *)
let write loc value mem =
  let* () = check_location loc mem in
  match loc.Location.obj with
  | Location.Stack _ -> (
      match mem.stack with
      | None -> Error (Unknown_object loc.Location.obj)
      | Some stack ->
          let storage = stack.storage in
          let storage =
            { storage with store = Location.LocMap.add loc value storage.store }
          in
          Ok { mem with stack = Some { stack with storage } } )
  | Location.Global _ ->
      let global = mem.global in
      let storage = global.storage in
      let storage =
        { storage with store = Location.LocMap.add loc value storage.store }
      in
      Ok { mem with global = { global with storage } }
  | Location.Heap _ ->
      let heap = mem.heap in
      let heap =
        { heap with store = Location.LocMap.add loc value heap.store }
      in
      Ok { mem with heap }

let string_of_bindings locals =
  let bindings =
    VarMap.bindings locals
    |> List.map (fun (vid, loc) ->
           Printf.sprintf "%s=%s" (Syntax.VarId.name vid)
             (Location.string_of_t loc))
  in
  "{" ^ String.concat ", " bindings ^ "}"

let string_of_store store =
  let entries =
    Location.LocMap.bindings store
    |> List.map (fun (loc, value) ->
           Location.string_of_t loc ^ "=" ^ Value.string_of_t value)
  in
  "{" ^ String.concat ", " entries ^ "}"

let string_of_values bindings storage =
  let entries =
    VarMap.bindings bindings
    |> List.map (fun (vid, loc) ->
           match Location.LocMap.find_opt loc storage.store with
           | Some value ->
               Printf.sprintf "%s |-> %s" (Syntax.VarId.name vid)
                 (Value.string_of_t value)
           | None -> Printf.sprintf "%s |-> ?" (Syntax.VarId.name vid))
  in
  "{" ^ String.concat ", " entries ^ "}"

let string_of_t mem =
  let stack_values =
    match mem.stack with
    | None -> "{}"
    | Some stack -> string_of_values stack.frame.locals stack.storage
  in
  if VarMap.is_empty mem.global.bindings then stack_values
  else
    let global_values =
      string_of_values mem.global.bindings mem.global.storage
    in
    "global " ^ global_values ^ "\nstack  " ^ stack_values

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
  | Invalid_next_object_id { area; next_object_id } ->
      let area =
        match area with
        | Stack_area -> "stack"
        | Global_area -> "global"
        | Heap_area -> "heap"
      in
      Printf.sprintf "invalid next object id in %s storage: %d" area
        next_object_id
  | Invalid_object_area { expected; object_id } ->
      let expected =
        match expected with
        | Stack_area -> "stack"
        | Global_area -> "global"
        | Heap_area -> "heap"
      in
      Printf.sprintf "object %s is not in %s storage"
        (Location.string_of_object_id object_id)
        expected
  | Invalid_object_id { object_id; next_object_id } ->
      Printf.sprintf "invalid object id %s with next id %d"
        (Location.string_of_object_id object_id)
        next_object_id
  | Object_size_mismatch { object_id; expected; actual } ->
      Printf.sprintf "object size mismatch for %s: expected %d, got %d"
        (Location.string_of_object_id object_id)
        expected actual
  | Invalid_binding_scope { variable; expected } ->
      let scope =
        match expected with
        | Syntax.VarId.Global -> "global"
        | Syntax.VarId.Function function_name -> "function " ^ function_name
      in
      Printf.sprintf "invalid memory binding scope for %s: expected %s"
        (Syntax.VarId.name variable) scope
  | Invalid_binding_location { variable; location } ->
      Printf.sprintf "invalid memory binding for %s: %s"
        (Syntax.VarId.name variable)
        (Location.string_of_t location)
  | Duplicate_binding_location location ->
      "duplicate memory binding location: " ^ Location.string_of_t location
  | Invalid_stored_location location ->
      "invalid stored location: " ^ Location.string_of_t location
  | Stored_value_type_mismatch { location; typ; value } ->
      Printf.sprintf "stored value type mismatch at %s: %s contains %s"
        (Location.string_of_t location)
        (Typ.string_of_t typ) (Value.string_of_t value)
