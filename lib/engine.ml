open Base
open Result.Let_syntax

let add_definition (u : Universe.t) key (d : Fact.t) :
    (Universe.t, string) Result.t =
  if Option.is_some (Map.find u key) then Result.fail "duplicate"
  else
    match Fact.get_term d with
    (* axiom. nothing to check *)
    | None -> Ok (Map.set u ~key ~data:d)
    (* definition. assert term : type *)
    | Some term ->
        let%bind _ =
          Kernel.check u (Fact.get_context d) term
            (Fact.get_type d)
        in
        Ok (Map.set u ~key ~data:d)
