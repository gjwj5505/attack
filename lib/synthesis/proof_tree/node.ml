module Node = struct
  type t = {
    id: int;
    mutable parent: t option;
    mutable children: t list;
    mutable formula: string option;
  }

  let create id =
    { id; parent = None; children = []; formula = None }

  let add_child parent child =
    child.parent <- Some parent;
    parent.children <- child :: parent.children

  let set_formula node formula =
    node.formula <- Some formula

end