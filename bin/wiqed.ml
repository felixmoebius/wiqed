open Core
open Libwiqed

let check_file ~trace file =
  let input = Input.from_file file in
  match Machine.verify ~trace input with
  | Error e -> print_endline e
  | Ok _ -> print_endline "done"

let command =
  Command.basic
    ~summary:"WIQED proof machine"
    ~readme:(fun () -> 
      "Toy theorem prover based on the calculus of constructions")
    Command.Let_syntax.(
      let%map_open trace = 
        flag "-trace" no_arg ~doc:" print derivation"
      and filename =
        anon (maybe_with_default "-" ("filename" %: Filename.arg_type))
      in
      fun () -> check_file ~trace filename
    )

let () =
  Command.run ~version:"1.0" ~build_info:"wiqed" command