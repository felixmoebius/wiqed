open Core
open Result.Let_syntax

let add_axiom universe key axiom =
    if Universe.is_unique universe key
    then
    let axioms = Map.set universe.axioms ~key ~data: axiom in
    Result.return {universe with axioms}
    else
    Result.fail (sprintf "definition %s, name already exists" key)

let add_definition universe key definition =
    if Universe.is_unique universe key
    then
    let definitions = Map.set universe.definitions ~key ~data: definition in
    Result.return { universe with definitions }
    else
    Result.fail (sprintf "definition %s, name already exists" key)

let add_theorem universe key theorem =
    if not (Universe.is_unique universe key)
    then Result.fail (sprintf "theorem %s, name already exists" key)
    else 
    let%bind () = Kernel.check universe 
    (Theorem.get_context theorem)
    (Theorem.get_proof theorem)
    (Theorem.get_proposition theorem) in
    let theorems = Map.set universe.theorems ~key ~data: theorem in
    Result.return { universe with theorems }

let process_toplevel (name, toplevel) universe =
  match toplevel with
  | Ast.Theorem t -> add_theorem universe name t
  | Ast.Axiom f -> add_axiom universe name f
  | Ast.Definition d -> add_definition universe name d

let verify (input : Input.t) =
  let%bind prog = Astgen.parse input.lexbuf in
  let ast = Lowering.lower prog in
  let rec loop tl universe =
    match tl with
    | [] -> Result.return universe
    | t :: tl' -> 
      printf "checking %s\n" (fst t);
      let%bind u = process_toplevel t universe in
      loop tl' u
  in
  loop ast Universe.empty
