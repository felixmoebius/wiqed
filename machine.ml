open Base
open Result.Let_syntax

let verify_all defs universe =
  let rec loop dl u = 
    match dl with
    | [] -> Result.return ()
    | (name, d) :: dl' ->
        let%bind u' = Engine.add_definition u name d in
        loop dl' u'
  in 
  loop defs universe


let verify (input : Input.t) : (unit, string) Result.t =
  let%bind prog = Astgen.parse input.lexbuf in
  let defs = Lowering.lower prog in
  verify_all defs Universe.empty

  