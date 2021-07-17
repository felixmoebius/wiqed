open Core
open Libwiqed

let do_hash file =
  Md5.digest_file_blocking file
  |> Md5.to_hex
  |> print_endline

let check_file file =
  let input = Input.from_file file in
  match Machine.verify input with
  | Error e -> print_endline e
  | Ok () -> print_endline "success"


let command =
  Command.basic
    ~summary:"WIQED proof machine"
    ~readme:(fun () -> "More detailed information")
    Command.Param.(
     map (anon ("filename" %: string))
       ~f:(fun filename -> (fun () -> check_file filename)))

let () =
  Command.run ~version:"1.0" ~build_info:"RWO" command