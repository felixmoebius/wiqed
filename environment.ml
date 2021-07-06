open Base

type definition = {
  name : string;
  args : (string * Term.t) list;
  term : Term.t option;
  typ' : Term.t;
}

type t = definition list

let lookup (e : t) s =
  let r = List.find e ~f:(fun d -> equal_string s d.name) in
  Result.of_option r ~error:(s ^ " not in env")