
type t = {
  filename : string;
  lexbuf : Lexing.lexbuf;
}

let from_string s =
  let filename = "string" in
  let lexbuf = Lexing.from_string s in
  { filename; lexbuf }