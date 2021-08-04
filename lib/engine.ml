open Base
open Result.Let_syntax

let add_fact (u : Universe.t) key (d : Fact.t) :
    (Universe.t, string) Result.t =
  if not (Universe.is_unique u key) then Result.fail "duplicate"
  else
    match Fact.get_term d with
    (* axiom. nothing to check *)
    | None -> Ok (Universe.add_fact u key d)
    (* theorem. assert term : type *)
    | Some term ->
        let%bind _ =
          Kernel.check u (Fact.get_context d) term
            (Fact.get_type d)
        in
        Ok (Universe.add_fact u key d)
