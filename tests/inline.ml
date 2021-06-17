open Base
open Stdio
open Typing

let print_exp e = print_endline (string_of_exp e)

let chk_exp ctx exp = match (normalized_type_of ctx exp) with
  | Error(e) -> print_endline e
  | Ok(e)  -> print_exp e

let bottom = Pi(Star,Bound(0))

let%expect_test _ =
  print_exp (Lambda(Pi(Free("x"),Bound(0)), Bound(0)));
  [%expect{| (lambda (Pi x . 0) . 0) |}];
  print_exp (Bound(0));
  [%expect{| 0 |}];
  chk_exp [] Star;
  [%expect{| Box |}];
  chk_exp [] (Pi(Star, Bound(0)));
  [%expect{||}];
  chk_exp [] Box;
  [%expect{| Box is not typeable |}];
  chk_exp [("P", Pi(Free("S"),Star)); ("S", Star)]
    (Lambda(Free("S"),Pi(App(Free("P"),Bound(0)),bottom)));
  [%expect{| (Pi S . *) |}]
  
