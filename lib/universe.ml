open Base
open Core

type t = {
    definitions: (string, Definition.t, String.comparator_witness) Map.t;
    theorems: (string, Theorem.t, String.comparator_witness) Map.t;
    axioms: (string, Axiom.t, String.comparator_witness) Map.t
}

let create () : t = 
    let definitions = Map.empty (module String)
    and theorems = Map.empty (module String)
    and axioms = Map.empty (module String)
    in
    { definitions; theorems; axioms }

let empty : t = create ()

let find_theorem (u : t) (s : string) = 
    let error = "there is no theorem named " ^ s ^ " in the universe" in
    Result.of_option (Map.find u.theorems s) ~error

let find_axiom(u : t) (s : string) = 
    let error = "there is no axiom named " ^ s ^ " in the universe" in
    Result.of_option (Map.find u.axioms s) ~error

let find_definition (u : t) (s : string) = 
    let error = "there is no definition named " ^ s ^ " in the universe" in
    Result.of_option (Map.find u.definitions s) ~error

let find (u : t) (s : string) =
    match find_theorem u s with
    | Ok t -> `Theorem t
    | Error _ ->
    (
        match find_axiom u s with
        | Ok a -> `Axiom a
        | Error _ ->
        (
            match find_definition u s with
            | Ok d -> `Definition d
            | Error _ -> `Not_found
        )
    )

let is_unique universe key =
    (Option.is_none (Map.find universe.definitions key)) &&
    (Option.is_none (Map.find universe.theorems key)) &&
    (Option.is_none (Map.find universe.axioms key))

(* let add_axiom universe key axiom =
    if is_unique universe key
    then
    let axioms = Map.set universe.axioms ~key ~data: axiom in
    Result.return {universe with axioms}
    else
    Result.fail (sprintf "definition %s, name already exists" key)

let add_definition universe key definition =
    if is_unique universe key
    then
    let definitions = Map.set universe.definitions ~key ~data: definition in
    Result.return { universe with definitions }
    else
    Result.fail (sprintf "definition %s, name already exists" key)

let add_theorem universe key theorem =
    if not (is_unique universe key)
    then Result.fail (sprintf "theorem %s, name already exists" key)
    else *)


