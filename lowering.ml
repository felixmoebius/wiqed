open Base

let lower_expression (e : Syntax.expression) : Term.t =
  let rec lower = function
    | Syntax.Box -> Term.Box
    | Syntax.Star -> Term.Star
    | Syntax.Free x -> Term.Free x
    | Syntax.Index i -> Term.Bound i
    | Syntax.Lambda (l, r) -> Term.Lambda (lower l, lower r)
    | Syntax.Pi (l, r) -> Term.Pi (lower l, lower r)
    | Syntax.Application (l, r) -> Term.App (lower l, lower r)
    | Syntax.Instance (n, args) -> Term.Def (n, List.map args ~f:lower)
  in
  lower e

let lower_theorem (t : Syntax.theorem) : string * Definition.t =
  let context : Context.t =
    List.map t.parameter_list ~f:(fun (name, exp) ->
        (name, lower_expression exp))
  and term = lower_expression t.proof
  and typ = lower_expression t.proposition in
  (t.name, Definition.make_theorem ~context ~term ~typ)

let lower_axiom (a : Syntax.axiom) : string * Definition.t =
  let context : Context.t =
    List.map a.parameter_list ~f:(fun (name, exp) ->
        (name, lower_expression exp))
  and typ = lower_expression a.proposition in
  (a.name, Definition.make_axiom ~context ~typ)

let lower_toplevel = function
  | Syntax.Theorem t -> lower_theorem t
  | Syntax.Axiom a -> lower_axiom a

let lower = List.map ~f:lower_toplevel
