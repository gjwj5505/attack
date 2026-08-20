type result =
  | Valid
  | Invalid of string

let ok = Valid
let error msg = Invalid msg

let ( >>= ) result next =
  match result with
  | Valid -> next ()
  | Invalid _ as error -> error

let check_memory_well_formed label memory =
  match Memory.check_well_formed memory with
  | Ok () -> ok
  | Error error ->
      Invalid
        (label ^ ": malformed memory: " ^ Memory.string_of_error error)

let check_memory label expected actual =
  check_memory_well_formed (label ^ " expected") expected >>= fun () ->
  check_memory_well_formed (label ^ " actual") actual >>= fun () ->
  if expected = actual then ok else error (label ^ ": memory mismatch")

let check_value label expected actual =
  if expected = actual then ok else error (label ^ ": value mismatch")

let check_location label expected actual =
  if expected = actual then ok else error (label ^ ": location mismatch")

let check_control label expected actual =
  if expected = actual then ok else error (label ^ ": control mismatch")

let check_int_value label = function
  | Value.Int { ikind = Typ.IInt; _ } -> ok
  | value ->
      error (label ^ ": expected int value, got " ^ Value.string_of_t value)

let check_expected_memory label actual = function
  | Ok expected -> check_memory label expected actual
  | Error message -> error (label ^ ": " ^ message)

let rec check_list check = function
  | [] -> ok
  | item :: items ->
      check item >>= fun () ->
      check_list check items

let rec check_function_arguments label formals arguments =
  match formals, arguments with
  | [], [] -> ok
  | formal :: formals, argument :: arguments ->
      if formal.Syntax.vtype <> Typ.TInt Typ.IInt then
        error
          (label ^ ": formal type is outside the int-only subset: "
         ^ SyntaxUtil.string_of_var formal)
      else
        check_int_value
          (label ^ " " ^ SyntaxUtil.var_name formal)
          argument
        >>= fun () ->
        check_function_arguments label formals arguments
  | [], _ :: _ | _ :: _, [] -> error (label ^ ": arity mismatch")

let rec bind_expected_formals formals arguments memory =
  match formals, arguments with
  | [], [] -> Ok memory
  | formal :: formals, argument :: arguments -> (
      match Memory.bind_local formal argument memory with
      | Ok (_, memory) ->
          bind_expected_formals formals arguments memory
      | Error error -> Error (Memory.string_of_error error) )
  | [], _ :: _ | _ :: _, [] -> Error "arity mismatch"

let rec allocate_expected_locals locals memory =
  match locals with
  | [] -> Ok memory
  | local :: locals -> (
      match Memory.allocate_local local memory with
      | Ok (_, memory) -> allocate_expected_locals locals memory
      | Error error -> Error (Memory.string_of_error error) )

let expected_function_body_input ~formals ~locals arguments memory =
  let memory = Memory.enter_function memory in
  match bind_expected_formals formals arguments memory with
  | Error error -> Error error
  | Ok memory -> allocate_expected_locals locals memory

let string_of_result = function
  | Valid -> "ok"
  | Invalid message -> message
