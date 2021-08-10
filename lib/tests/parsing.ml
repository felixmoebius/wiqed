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
    Definition
      Name(x1: a1) : a2
    End |};
  [%expect {|
    Definition
      Name(x1: a1) : a2
    End
     |}];

  test {|
    Definition
      Name(x1: a1) := x2 : a2
    End |};
  [%expect {|
    Definition
      Name(x1: a1) := x2 : a2
    End
     |}];

  test {|
    Definition
      Name1(x1: a1) := x2 : a2
    End 
    
    Definition
      Name2(x1: a1) := x2 : a2
    End |};
  [%expect {|
    Definition
      Name1(x1: a1) := x2 : a2
    End

    Definition
      Name2(x1: a1) := x2 : a2
    End
     |}];

  test {|
    Definition
      Name(x1: a1) := lambda a. x : a2
    End |};
  [%expect {|
    Definition
      Name(x1: a1) := (lambda a . x) : a2
    End
     |}];

  test {|
    Definition
      Name(x1: a1) := lambda a. 1 0 : a2
    End |};
  [%expect {|
    Definition
      Name(x1: a1) := (lambda a . (1 0)) : a2
    End
    |}];

  test {|
    Definition
      Name(x1: a1) := (pi a. 1 (lambda b. 0 1)) x y : a2
    End |};
  [%expect {|
    Definition
      Name(x1: a1) := (((Pi a . (1 (lambda b . (0 1)))) x) y) : a2
    End
    |}];

  test {|
    Definition
      Name(a1: *, x1: a1) := x1 : a1
    End |};
  [%expect {|
    Definition
      Name(a1: *, x1: a1) := x1 : a1
    End
     |}];



