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

  test "\n"; [%expect {| |}];
  test ""; [%expect {| |}];
  test " \t \n"; [%expect {| |}];

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

  test {|
    Theorem
      Name1(x1: a1) : a2
    Proof
      x2
    Qed 
    
    Theorem
      Name2(x1: a1) : a2
    Proof
      x2
    Qed |};
  [%expect {|
    Theorem
      Name1(x1: a1) : a2
    Proof
      x2
    Qed

    Theorem
      Name2(x1: a1) : a2
    Proof
      x2
    Qed |}];

  test {|
    Theorem
      Name(x1: a1) : a2
    Proof
      lambda a. x
    Qed |};
  [%expect {|
    Theorem
      Name(x1: a1) : a2
    Proof
      (lambda a . x)
    Qed |}];

  test {|
    Theorem
      Name(x1: a1) : a2
    Proof
      lambda a. 1 0
    Qed |};
  [%expect {|
    Theorem
      Name(x1: a1) : a2
    Proof
      (lambda a . (1 0))
    Qed |}];

  test {|
    Theorem
      Name(x1: a1) : a2
    Proof
      (pi a. 1 (lambda b. 0 1)) x y
    Qed |};
  [%expect {|
    Theorem
      Name(x1: a1) : a2
    Proof
      (((Pi a . (1 (lambda b . (0 1)))) x) y)
    Qed |}];
  test {|
    Theorem
      Name(a1: *, x1: a1) : a1
    Proof
      x1
    Qed |};
  [%expect {|
    Theorem
      Name(a1: *, x1: a1) : a1
    Proof
      x1
    Qed |}];



