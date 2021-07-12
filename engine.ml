open Base
open Result.Let_syntax

let add_definition (u : Universe.t) key (d : Definition.t) :
    (Universe.t, string) Result.t =
  if Option.is_some (Map.find u key) then Result.fail "duplicate"
  else
    match Definition.get_term d with
    | None -> Ok (Map.set u ~key ~data:d)
    | Some term ->
        let%bind _ =
          Kernel.check [] (Definition.get_context d) 0 term
            (Definition.get_type d)
        in
        Ok (Map.set u ~key ~data:d)
