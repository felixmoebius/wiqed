open Base

type t = Context.t * Term.t option * Term.t

let make_definition ~context ~term ~typ : t =
(context, Some(term), typ)

let make_axiom ~context ~typ : t =
(context, None, typ)

let get_context ((c, _, _) : t) = c
let get_term ((_, t, _) : t) = t
let get_type ((_, _, t) : t) = t
