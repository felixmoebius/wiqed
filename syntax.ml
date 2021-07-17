(* This file contains a parse tree for the wiqed language. *)

open Base
open Core

type expression =
  | Box
  | Star
  | Free of string
  | Index of int
  | Lambda of expression * expression
  | Pi of expression * expression
  | Application of expression * expression
  | Instance of string * argument list

and argument = expression

type parameter = string * expression

type theorem = {
  name : string;
  parameter_list : parameter list;
  proposition : expression;
  proof : expression;
}

type axiom = {
  name : string;
  parameter_list : parameter list;
  proposition : expression;
}

type toplevel = Theorem of theorem | Axiom of axiom

type prog = toplevel list

let rec pp_expression = function
  | Box -> "#"
  | Star -> "*"
  | Free id -> id
  | Index i -> Int.to_string i
  | Lambda (t, e) ->
      sprintf "(lambda %s . %s" (pp_expression t) (pp_expression e)
  | Pi (t, e) -> sprintf "(Pi %s . %s)" (pp_expression t) (pp_expression e)
  | Application (l, r) -> sprintf "(%s %s)" (pp_expression l) (pp_expression r)
  | Instance (n, a) ->
      let pp_args =
        List.fold a ~init:"" ~f:(fun acc x ->
            if String.equal acc "" then pp_expression x
            else sprintf "%s, %s" acc (pp_expression x))
      in
      sprintf "%s(%s)" n pp_args

and pp_parameter (n, e) = sprintf "%s: %s" n (pp_expression e)

and pp_parameter_list pl =
  List.fold pl ~init:"" ~f:(fun acc p ->
      if String.is_empty acc then pp_parameter p
      else sprintf "%s, %s" acc (pp_parameter p))

and pp_theorem (t : theorem) =
  sprintf "Theorem\n  %s(%s) : %s\nProof\n  %s\nQed" t.name
    (pp_parameter_list t.parameter_list)
    (pp_expression t.proposition)
    (pp_expression t.proof)

and pp_axiom (a : axiom) =
  sprintf "Axiom\n  %s(%s) : %s\nDone" a.name
    (pp_parameter_list a.parameter_list)
    (pp_expression a.proposition)

and pp_toplevel = function Theorem t -> pp_theorem t | Axiom a -> pp_axiom a

and pp_prog p =
  List.fold p ~init:"" ~f:(fun acc x ->
      if String.is_empty acc then pp_toplevel x
      else sprintf "%s\n\n%s" acc (pp_toplevel x))

