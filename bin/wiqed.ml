open Core
open Libwiqed

let check_file file =
  let input = Input.from_file file in
  match Machine.verify input with
  | Error e -> print_endline e
  | Ok _ -> print_endline "done"


let command =
  Command.basic
    ~summary:"WIQED proof machine"
    ~readme:(fun () -> "More detailed information")
    Command.Param.(
     map (anon ("filename" %: string))
       ~f:(fun filename -> (fun () -> check_file filename)))

let () =
  Command.run ~version:"1.0" ~build_info:"wiqed" command