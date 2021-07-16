(* This file contains a parse tree for the wiqed language. *)

open Base

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

