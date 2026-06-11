module Json = Yojson.Safe
module Result = Sparrow_result

let json_member name json = Json.Util.member name json

let json_string name json = Json.Util.to_string (json_member name json)

let json_bool name json = Json.Util.to_bool (json_member name json)

let json_int name json = Json.Util.to_int (json_member name json)

let json_string_opt name json =
  match json_member name json with
  | `Null -> None
  | value -> Some (Json.Util.to_string value)

let bound_of_string = function
  | "-oo" -> Result.Neg_inf
  | "+oo" -> Result.Pos_inf
  | s -> Result.Int (int_of_string s)

let interval_of_string s =
  if s = "bot" then Result.Bot
  else
    let len = String.length s in
    if len < 5 || s.[0] <> '[' || s.[len - 1] <> ']' then
      invalid_arg ("invalid interval: " ^ s)
    else
      let body = String.sub s 1 (len - 2) in
      match String.split_on_char ',' body with
      | [ lo; hi ] ->
          Result.Interval
            ( bound_of_string (String.trim lo),
              bound_of_string (String.trim hi) )
      | _ -> invalid_arg ("invalid interval: " ^ s)

let value_of_json json =
  let itv = json_string "itv" json |> interval_of_string in
  let raw = json_string "raw" json in
  Result.{ itv; raw }

let binding_of_json json =
  Result.
    { loc = json_string "loc" json; value = json_member "value" json |> value_of_json }

let mem_of_json json =
  Result.
    {
      is_bot = json_bool "is_bot" json;
      bindings =
        json_member "bindings" json |> Json.Util.to_list |> List.map binding_of_json;
    }

let node_state_of_json json =
  Result.{ node = json_string "node" json; mem = json_member "mem" json |> mem_of_json }

let alarm_summary_of_json json =
  Result.
    {
      total = json_int "total" json;
      proven = json_int "proven" json;
      unproven = json_int "unproven" json;
      bot = json_int "bot" json;
    }

let analysis_of_string text =
  let json = Json.from_string text in
  Result.
    {
      file = json_string "file" json;
      analysis = json_string "analysis" json;
      main_exit_node = json_string_opt "main_exit_node" json;
      alarms = json_member "alarms" json |> alarm_summary_of_json;
      input = json_member "input" json |> Json.Util.to_list |> List.map node_state_of_json;
      output = json_member "output" json |> Json.Util.to_list |> List.map node_state_of_json;
    }
