open Base
open Result.Let_syntax

type t = Term.t * string list

let instantiate ((term, params) : t) (args : Term.t list) =
  let%bind z =
    match List.zip params args with
    | Ok z' -> Result.return z'
    | _ -> Result.fail "todo"
  in
  Result.return (List.fold z ~init:term ~f:(fun t (p, a) -> Term.subst t p a))
