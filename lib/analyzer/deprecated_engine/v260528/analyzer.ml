type aval = Abs_domain.Abs_val.t

type aenv = Abs_domain.Abs_env.t

type sem = Abs_domain.Abs_sem.t

let analysis_sem = Analyzer_engine.analysis_sem

let analysis = Analyzer_engine.analysis

let exit_aenv = Analyzer_engine.exit_aenv

let find = Abs_domain.Abs_env.find

let contains_concrete cval aval = Itv.(singleton cval <= aval)

let is_singleton cval aval = Itv.equal aval (Itv.singleton cval)

let is_top = Abs_domain.Abs_val.is_top

let is_unbounded = function
  | Itv.Bot -> false
  | Itv.Itv (Itv.Bound.N_inf, _) | Itv.Itv (_, Itv.Bound.P_inf) -> true
  | Itv.Itv _ -> false

let string_of_aval = Abs_domain.Abs_val.string_of_t

let string_of_aenv = Abs_domain.Abs_env.string_of_t

let string_of_analysis_sem = Visualizer.string_of_analysis_sem

let print_analysis_sem = Visualizer.print_analysis_sem
