type t = Context.t * Term.t

let make ~context ~proposition = (context, proposition)
let get_context axiom = fst axiom
let get_proposition axiom = snd axiom