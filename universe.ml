open Base

type t = (string, Definition.t, String.comparator_witness) Map.t

let create () : t = Map.empty (module String)
