open Core
open Lexer
open Lexing

let get_position lexbuf =
  let pos = lexbuf.lex_curr_p in
  sprintf "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse lexbuf : (Syntax.prog, string) result =
  try Result.return (Parser.prog Lexer.read lexbuf) with
  | SyntaxError msg ->
      let s = sprintf "%s: %s" (get_position lexbuf) msg in
      Result.fail s

  | Parser.Error ->
      let s = sprintf  "%s: syntax error" (get_position lexbuf) in
      Result.fail s

  | _ -> 
      let s = sprintf "%s: unknown error" (get_position lexbuf) in
      Result.fail s
