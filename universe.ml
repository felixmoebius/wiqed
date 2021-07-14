open Base

type t = (string, Definition.t, String.comparator_witness) Map.t

let create () : t = Map.empty (module String)

let find (u : t) (s : string) = 
    let error = "there is no definition named " ^ s ^ " in the universe" in
    Result.of_option (Map.find u s) ~error