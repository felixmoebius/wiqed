
type t =
  | Theorem of Context.t * Term.t * Term.t
  | Axiom of Context.t * Term.t

let get_context = function
  | Theorem (c, _, _) -> c
  | Axiom (c, _) -> c

let get_proposition = function
  | Theorem (_, _, p) -> p
  | Axiom (_, p) -> p