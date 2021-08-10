open Core
open Result.Let_syntax

let add_definition ~trace universe key definition =
  let%bind _ =
    match definition with
    | Definition.Theorem (context, proof, proposition) ->
        Kernel.check ~trace universe context proof proposition
    | Definition.Axiom (context, proposition) ->
        Result.map (Kernel.infer ~trace universe context proposition) ~f:(fun _ -> ())
  in
  Result.return (Universe.add universe key definition)

let verify ~trace (input : Input.t) =
  let%bind prog = Frontend.parse input.lexbuf in
  let ast = Lowering.lower prog in
  let rec loop tl universe =
    match tl with
    | [] -> Result.return universe
    | t :: tl' ->
        printf "checking %s" (fst t);
        let%bind u =
          match add_definition ~trace universe (fst t) (snd t) with
          | Ok x ->
              printf "...ok\n";
              Result.return x
          | Error e ->
              printf "...error\n";
              Result.fail e
        in
        loop tl' u
  in
  loop ast Universe.empty
