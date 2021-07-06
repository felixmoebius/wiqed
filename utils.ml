open Base

let first_err l ~f =
  let open Result in
  let rec loop = function
    | [] -> return ()
    | x :: l' -> f x >>= fun _ -> loop l'
  in
  loop l
