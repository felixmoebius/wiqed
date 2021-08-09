type t = Context.t * Term.t * Term.t

let make ~context ~proposition ~proof = (context, proof, proposition)
let get_context (c, _, _) = c
let get_proof (_, p, _) = p
let get_proposition (_, _, p) = p