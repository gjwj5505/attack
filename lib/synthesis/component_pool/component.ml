open Language.Syntax
open Language.BigStep

module type Payload = sig
  type t
end

module Make_component (Payload : Payload) = struct
  type payload = Payload.t

  type t = {
    payload : payload;
    score : float;
  }

  let make_with_score payload score = { payload; score }
  let payload t = t.payload
  let score t = t.score
end

module Exp_component = struct
  include Make_component (struct
    type t = Exp.t
  end)

  let make payload = make_with_score payload (Heuristic.score_current_exp payload)
end

module Cmd_component = struct
  include Make_component (struct
    type t = Cmd.t
  end)

  let make payload = make_with_score payload (Heuristic.score_current_cmd payload)
end

module Etree_component = struct
  include Make_component (struct
    type t = etree
  end)

  let make payload =
    make_with_score payload (Heuristic.score_current_etree payload)
end

module Ctree_component = struct
  include Make_component (struct
    type t = ctree
  end)

  let make payload =
    make_with_score payload (Heuristic.score_current_ctree payload)
end
