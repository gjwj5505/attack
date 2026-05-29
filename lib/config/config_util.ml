open Language

let attack () =
  Config.
    {
      vars;
      target_var;
      ints;
      value_range;
      uops;
      bops;
      heuristic_name;
      analyzer_name;
      seed;
    }

let values_in_range (lo, hi) =
  if lo > hi then [] else List.init (hi - lo + 1) (fun i -> lo + i)

let valid_env cfg cenv =
  let lo, hi = cfg.Config.value_range in
  let vars_in_range =
    List.for_all
      (fun x ->
        let cval = Environment.lookup x cenv in
        lo <= cval && cval <= hi)
      cfg.Config.vars
  in
  let only_config_vars =
    Environment.VarMap.bindings cenv
    |> List.for_all (fun (x, _) -> List.mem x cfg.Config.vars)
  in
  vars_in_range && only_config_vars

let bounded_envs cfg =
  let values = values_in_range cfg.Config.value_range in
  let rec aux = function
    | [] -> [ Environment.empty ]
    | x :: xs ->
        aux xs
        |> List.concat_map (fun cenv ->
               List.map (fun cval -> Environment.update x cval cenv) values)
  in
  aux cfg.Config.vars

let is_in_bound cfg x =
  let lo, hi = cfg.Config.value_range in
  lo <= x && x <= hi
