{
open Lexing
open Parser

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = pos.pos_cnum;
               pos_lnum = pos.pos_lnum + 1
    }
}

let index    = ['0'-'9'] ['0'-'9']*
let free     = ['a'-'z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let global   = ['A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let white    = [' ' '\t']+
let newline  = '\r' | '\n' | "\r\n"

rule read =
  parse
  | white     { read lexbuf }
  | newline   { next_line lexbuf; read lexbuf }
  | "lambda"  { LAMBDA }
  | '\\'      { LAMBDA }
  | "pi"      { PI }
  | "forall"  { PI }
  | "Theorem" { THEOREM }
  | "Axiom"   { AXIOM }
  | "Definition"  { DEFINITION }
  | ":="      { AS }
  | "Proof"   { PROOF }
  | "Qed"     { QED }
  | "Done"    { DONE }
  | '.'       { DOT }
  | '('       { LPAREN }
  | ')'       { RPAREN }
  | '*'       { STAR }
  | '#'       { BOX }
  | ':'       { COLON }
  | ','       { COMMA }
  | free      { FREE (Lexing.lexeme lexbuf) }
  | global    { GLOBAL (Lexing.lexeme lexbuf) }
  | index     { INDEX (int_of_string (Lexing.lexeme lexbuf)) }
  | _ { raise (SyntaxError ("Unexpected character: " ^ Lexing.lexeme lexbuf)) }
  | eof       { EOF }
