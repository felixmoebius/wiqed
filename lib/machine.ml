open Core
open Result.Let_syntax

let add_definition universe key definition =
  let%bind _ = match definition with
  | Definition.Theorem (context, proof, proposition) ->
      Kernel.check universe context proof proposition
  | Definition.Axiom (context, proposition) ->
      Result.map (Kernel.infer universe context proposition) ~f:(fun _ -> ())
  in
  Result.return (Universe.add universe key definition)

let verify (input : Input.t) =
  let%bind prog = Astgen.parse input.lexbuf in
  let ast = Lowering.lower prog in
  let rec loop tl universe =
    match tl with
    | [] -> Result.return universe
    | t :: tl' -> 
      printf "checking %s\n" (fst t);
      let%bind u = add_definition universe (fst t) (snd t) in
      loop tl' u
  in
  loop ast Universe.empty
