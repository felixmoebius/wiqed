open Base

type facts = (string, Fact.t, String.comparator_witness) Map.t
type defs = (string, Fact.t, String.comparator_witness) Map.t

type t = {
    facts: facts;
    defs: defs
}

let create () : t = 
    let facts = Map.empty (module String)
    and defs = Map.empty (module String)
    in
    { facts; defs }

let empty : t = create ()

let find_fact (u : t) (s : string) = 
    let error = "there is no theorem or axiom named " ^ s ^ " in the universe" in
    Result.of_option (Map.find u.facts s) ~error

let find_def (u : t) (s : string) = 
    let error = "there is no definition named " ^ s ^ " in the universe" in
    Result.of_option (Map.find u.defs s) ~error

let add_fact (u : t) key (f : Fact.t) : t =
    let n = Map.set u.facts ~key ~data: f in
    { facts = n; defs = u.defs }

let is_unique (u : t) key =
    (Option.is_none (Map.find u.facts key)) &&
    (Option.is_none (Map.find u.defs key))

