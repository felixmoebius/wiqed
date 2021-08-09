open Base
open Core

type t = (string, Definition.t, String.comparator_witness) Map.t

let create () : t = Map.empty (module String)

let empty : t = create ()

let find (u : t) (s : string) = 
    let error = sprintf "no definition named %s in universe" s in
    Result.of_option (Map.find u s) ~error

let is_unique universe key = Option.is_none (Map.find universe key)

let add (u : t) key data = Map.set u ~key ~data
