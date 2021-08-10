open Base

type t =
  | Box
  | Star
  | Free of string
  | Bound of int
  | Lambda of t * t
  | Pi of t * t
  | App of t * t
  | Inst of string * t list

let rec string_of_exp exp =
  let open String in
  match exp with
  | Box -> "Box"
  | Star -> "*"
  | Free id -> id
  | Bound i -> Int.to_string i
  | Lambda (t, e) ->
      concat [ "(lambda "; string_of_exp t; " . "; string_of_exp e; ")" ]
  | Pi (t, e) -> concat [ "(Pi "; string_of_exp t; " . "; string_of_exp e; ")" ]
  | App (l, r) -> concat [ "("; string_of_exp l; " "; string_of_exp r; ")" ]
  | Inst (n, args) -> Core.sprintf "%s(%s)" n (string_of_exp_list args)

and string_of_exp_list l =
  List.fold l ~init:"" ~f: (fun acc e ->
    let s = string_of_exp e in
    if String.is_empty acc then s
    else Core.sprintf "%s, %s" acc s)

(* replace all bound variables in t at de Bruijn index k 
with the term u *)
let rec _open t k u =
  match t with
  (* [], *, name *)
  | Box | Star | Free _ -> t
  (* lambda _ : typ . e *)
  | Lambda (typ, e) -> Lambda (_open typ k u, _open e (k + 1) u)
  (* de Bruijn index i *)
  | Bound i -> if equal i k then u else t
  (* name(args) *)
  | Inst (name, args) -> Inst (name, List.map args ~f:(fun e -> _open e k u))
  (* t1 t2 *)
  | App (t1, t2) -> App (_open t1 k u, _open t2 k u)
  (* Pi _ : typ . e *)
  | Pi (typ, e) -> Pi (_open typ k u, _open e (k + 1) u)

(* replace all bound variables at de Bruijn index 0.
this means replacing all 'dangling' indices that we get by only
looking at the right hand side of an abstraction *)
let open0 e u = _open e 0 u

(* bind all occurences of free variable x in t to binder 
at de Bruijn index k. *)
let rec _close t k x =
  match t with
  (* [], *, i *)
  | Box | Star | Bound _ -> t
  (* name *)
  | Free name -> if String.equal x name then Bound k else t
  (* name(args) *)
  | Inst (name, args) -> Inst (name, List.map args ~f:(fun e -> _close e k x))
  (* t1 t2 *)
  | App (t1, t2) -> App (_close t1 k x, _close t2 k x)
  (* lambda _ : typ . e *)
  | Lambda (typ, e) -> Lambda (_close typ k x, _close e (k + 1) x)
  (* Pi _ : typ . e *)
  | Pi (typ, e) -> Pi (_close typ k x, _close e (k + 1) x)

(* bind all occurences of free variable x in t to the binder
at de Bruijn index 0. this is can be used to abstract over a
variable by binding the free variable to index 0, thus producing
a 'dangling' de Bruijn index that gets bound when we put the
result into an abstraction *)
let close0 t x = _close t 0 x

let rec bump = function
  | Box -> Box | Star -> Star | Free x -> Free x
  | App (t1, t2) -> App (bump t1, bump t2)
  | Lambda (t1, t2) -> Lambda (bump t1, bump t2)
  | Pi (t1, t2) -> Pi (bump t1, bump t2)
  | Inst (n, a) -> Inst (n, List.map a ~f: bump)
  | Bound i -> Bound (i+1)

(* substitute free variable z in e with u *)
let rec subst e z u =
  match e with
  (* terminal *)
  | Box | Star | Bound _ -> e
  (* subst if z' = z *)
  | Free z' -> if equal_string z z' then u else e
  (* subst in subterms *)
  | App (t1, t2) -> App (subst t1 z u, subst t2 z u)
  | Lambda (typ, e') -> Lambda (subst typ z u, subst e' z (bump u))
  | Pi (typ, e') -> Pi (subst typ z u, subst e' z (bump u))
  (* subst in all arguments *)
  | Inst (n, a) -> Inst (n, List.map a ~f:(fun e' -> subst e' z u))

let subst_all (xu : (string * t) list) (a : t) =
  List.fold xu ~init:a ~f:(fun a' (x, u) -> subst a' x u)

let subst_range i xu a = subst_all (List.take xu i) a

