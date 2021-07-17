open Base
open Stdio

let parse_and_stringify s =
  let lexbuf = Lexing.from_string s in
  match Astgen.parse lexbuf with
  | Ok prog -> Syntax.pp_prog prog
  | Error e -> e

let parse_and_print s =
  print_endline (parse_and_stringify s)

let%expect_test _ =
  let test = parse_and_print in

  test "\n";
  [%expect {| |}];

  test {|
    Axiom
      Name(x1: a1) : a2
    Done |};
  [%expect {|
    Axiom
      Name(x1: a1) : a2
    Done |}];

  test {|
    Theorem
      Name(x1: a1) : a2
    Proof
      x2
    Qed |};
  [%expect {|
    Theorem
      Name(x1: a1) : a2
    Proof
      x2
    Qed |}];



