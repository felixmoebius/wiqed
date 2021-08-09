open Base

(* resmap *)
let first_err l ~f =
  let open Result in
  let rec loop = function
    | [] -> return ()
    | x :: l' -> f x >>= fun _ -> loop l'
  in
  loop l

let resfold l ~init ~f =
  let open Result in
  let rec loop xl acc =
    match xl with
    | [] -> return acc
    | x :: l' ->
      (match f acc x with
      | Ok r -> loop r l'
      | Error e -> Result.fail e
      )   
  in loop l init
