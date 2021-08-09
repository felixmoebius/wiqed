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
    | Syntax.Instance (n, args) -> Term.Inst (n, List.map args ~f:lower)
  in
  lower e

let lower_theorem (t : Syntax.theorem) =
  let context : Context.t =
    List.map t.parameter_list ~f:(fun (name, exp) ->
        (name, lower_expression exp))
  and proof = lower_expression t.proof
  and proposition = lower_expression t.proposition in
  Ast.Theorem (Theorem.make ~context ~proposition ~proof)

let lower_axiom (a : Syntax.axiom) =
  let context : Context.t =
    List.map a.parameter_list ~f:(fun (name, exp) ->
        (name, lower_expression exp))
  and proposition = lower_expression a.proposition in
  Ast.Axiom (Axiom.make ~context ~proposition)

let lower_definition (d : Syntax.definition) =
  Ast.Definition (lower_expression d.term, d.parameter_list)

let lower_toplevel = function
  | Syntax.Theorem t -> (t.name, lower_theorem t)
  | Syntax.Axiom a -> (a.name, lower_axiom a)
  | Syntax.Definition d -> (d.name, lower_definition d)

let lower (prog : Syntax.prog) = List.map prog ~f: lower_toplevel
