open Core

type t = { filename : string; lexbuf : Lexing.lexbuf }

let from_string s =
  let filename = "string" in
  let lexbuf = Lexing.from_string s in
  { filename; lexbuf }

let from_file filename =
  let inx = In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  { filename; lexbuf }
