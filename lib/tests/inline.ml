open Base
open Stdio
open Term

let print_exp e = print_endline (string_of_exp e)

let normalized_type_of = Kernel.infer_normalized Universe.empty

let chk_exp ctx exp =
  match normalized_type_of ctx exp with
  | Error e -> print_endline e
  | Ok e -> print_exp e

let bottom = Pi (Star, Bound 0)

let%expect_test _ =
  print_exp (Lambda (Pi (Free "x", Bound 0), Bound 0));
  [%expect {| (lambda (Pi x . 0) . 0) |}];
  print_exp (Bound 0);
  [%expect {| 0 |}];
  chk_exp [] Star;
  [%expect {| Box |}];
  chk_exp [] (Pi (Star, Bound 0));
  [%expect {| * |}];
  chk_exp [] Box;
  [%expect {| Box is not typeable at level (0) |}];
  chk_exp
    [ ("P", Pi (Free "S", Star)); ("S", Star) ]
    (Lambda (Free "S", Pi (App (Free "P", Bound 0), bottom)));
  [%expect {| (Pi S . *) |}];
  chk_exp [ ("S", Star) ] (Lambda (Pi (Free "S", Pi (Free "S", Star)), Bound 0));
  [%expect {| (Pi (Pi S . (Pi S . *)) . (Pi S . (Pi S . *))) |}];
  chk_exp [ ("S", Star) ]
    (Lambda
       ( Pi (Free "S", Pi (Free "S", Star)),
         Lambda (Free "S", App (App (Bound 1, Bound 0), Bound 0)) ));
  [%expect {| (Pi (Pi S . (Pi S . *)) . (Pi S . *)) |}];
  chk_exp [] (Lambda (Star, Lambda (Bound 0, Bound 0)));
  [%expect {| (Pi * . (Pi 0 . 1)) |}];
  chk_exp []
    (Lambda
       ( Star,
         Lambda
           ( Pi (Bound 0, Star),
             Lambda (Bound 1, Pi (App (Bound 1, Bound 0), bottom)) ) ));
  [%expect {| (Pi * . (Pi (Pi 0 . *) . (Pi 1 . *))) |}];
  chk_exp [ ("A", Star) ] (Pi (Free "A", Star));
  [%expect {| Box |}];
  chk_exp [ ("z", Free "A"); ("A", Star) ] (App (Pi (Free "A", Star), Free "z"));
  [%expect {| expected Pi abstraction at level (0) |}];
  chk_exp
    [ ("z", Free "A"); ("A", Star) ]
    (App (Lambda (Free "A", Star), Free "z"));
  [%expect {| Box is not typeable at level (3) |}];
  chk_exp [ ("A", Star) ] (Pi (Free "A", Star));
  [%expect {| Box |}];
  chk_exp [ ("A", Star) ] (Lambda (Free "A", Free "A"));
  [%expect {| (Pi A . *) |}];
  chk_exp
    [ ("z", Free "A"); ("A", Star) ]
    (App (Lambda (Free "A", Free "A"), Free "z"));
  [%expect {| * |}];
  chk_exp
    [ ("z", Free "A"); ("A", Star) ]
    (App (Lambda (Star, Free "A"), Free "A"));
  [%expect {| * |}];
  chk_exp [ ("z", Free "A"); ("A", Star) ] (Lambda (Star, Star));
  [%expect {| Box is not typeable at level (2) |}];
  chk_exp [] (Pi (Star, Star));
  [%expect {| Box |}];
  chk_exp [] (Pi (Star, Box));
  [%expect {| Box is not typeable at level (1) |}];
  chk_exp [ ("A", Star) ] (Pi (Free "A", Star));
  [%expect {| Box |}];
  chk_exp
    [ ("z", Free "A"); ("A", Star) ]
    (Pi (App (Lambda (Free "A", Free "A"), Free "z"), Star));
  [%expect {| Box |}]
