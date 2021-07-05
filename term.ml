open Base

type t =
  | Box
  | Star
  | Free   of string
  | Bound  of int
  | Lambda of t * t
  | Pi     of t * t
  | App    of t * t
  | Def    of string * (t list)

(* replace all bound variables in t at de Bruijn index k 
with the term u *)
let rec _open t k u = 
  match t with
  (* [], *, name *)
  | Box | Star | Free(_) -> t
  (* lambda _ : typ . e *)
  | Lambda(typ, e) -> Lambda(_open typ k u, _open e (k + 1) u)
  (* i *)
  | Bound(i) -> 
    if equal i k 
    then u 
    else t
  (* name(args) *)
  | Def(name, args) -> Def(name, List.map args 
    ~f: (fun e -> _open e k u))
  (* t1 t2 *)
  | App(t1, t2) -> App(_open t1 k u, _open t2 k u)
  (* Pi _ : typ . e *)
  | Pi(typ, e) -> Pi(_open typ k u, _open e (k + 1) u)

(* replace all bound variables at de Bruijn index 0.
this means replacing all 'dangling' indeces that we get by only
looking at the right hand side of an abstraction *)
let open0 e u = _open e 0 u

(* bind all occurences of free variable x in t to binder 
at de Bruijn index k. *)
let rec _close t k x =
  match t with
  (* [], *, i *)
  | Box | Star | Bound(_) -> t
  (* name *)
  | Free(name) -> 
    if String.equal x name 
    then Bound(k) 
    else t
  (* name(args) *)
  | Def(name, args) -> Def(name, List.map args 
    ~f: (fun e -> _close e k x))
  (* t1 t2 *)
  | App(t1, t2) -> App(_close t1 k x, _close t2 k x)
  (* lambda _ : typ . e *)
  | Lambda(typ, e) -> Lambda(_close typ k x, _close e (k + 1) x)
  (* Pi _ : typ . e *)
  | Pi(typ, e) -> Pi(_close typ k x, _close e (k + 1) x)
  
(* bind all occurences of free variable x in t to the binder
at de Bruijn index 0. this is can be used to abstract over a
variable by binding the free variable to index 0, thus producing
a 'dangling' de Bruijn index that gets bound when we put the
result into an abstraction *)
let close0 t x = _close t 0 x

(* normalize well-typed term *)
let rec normalize exp = 
  match exp with
  (* atom *)
  | Box | Star | Free(_) | Bound(_) -> exp
  (* normalize descendents *)
  | Lambda(typ, e) -> Lambda (normalize typ, normalize e)
  | Pi(typ, e) ->     Pi     (normalize typ, normalize e)
  (* beta reduction *)
  | App(f, x) ->
    (match normalize f with
    (* apply if we can... *)
    | Lambda(_, e) -> normalize (open0 e x)
    (* ...otherwise just return components *)
    | f' -> App(f', normalize x))

  | Def(_) -> 
    raise (Failure "unfold unimplemented")

(* substitute free variable z in e with u *)
let rec subst e z u =
  match e with
  (* atom *)
  | Box | Star | Bound(_) -> e
  (* subst if z' = z *)
  | Free(z') -> 
    if equal_string z z' 
    then u 
    else e
  (* subst in subterms *)
  | App(t1, t2)     -> App    (subst t1  z u, subst t2 z u)
  | Lambda(typ, e') -> Lambda (subst typ z u, subst e' z u)
  | Pi(typ, e')     -> Pi     (subst typ z u, subst e' z u)
  (* subst in all arguments *)
  | Def(n, a) ->
    Def(n, List.map a ~f: (fun e' -> subst e' z u))

(* check for term equality by testing for alpha-conversion.
the locally-nameless approach makes this very easy, because
we only need to recursively check the structure of the terms
and ensure that free variable names and bound variable de Bruijn
indeces match *)
let rec alpha_eq e1 e2 = match e1, e2 with
  (* atom *)
  | (Star, Star) | (Box, Box) -> true

  (* matching de Bruijn indeces *)
  | (Bound i1, Bound i2) -> equal_int i1 i2

  (* matching free variable names *)
  | (Free x1, Free x2) -> equal_string x1 x2

  (* equal iff descendents are equal *)
  | (Lambda(l1, r1), Lambda(l2, r2))
  | (Pi    (l1, r1), Pi    (l2, r2))
  | (App   (l1, r1), App   (l2, r2)) ->
    (alpha_eq l1 l2) && (alpha_eq r1 r2)

  (* definition name matches and all args are equal *)
  | (Def(n1, a1), Def(n2, a2)) ->
    List.(
    equal_string n1 n2 && (match (zip a1 a2) with
    | Unequal_lengths -> false
    | Ok(z) ->  for_all z ~f: (fun (x1, x2) -> alpha_eq x1 x2))
    )

  (* unequal in all other cases *)
  | _ -> false

(* check for beta-equality by checking the normalized term
for alpha-convertibility *)
let beta_eq e1 e2 = alpha_eq (normalize e1) (normalize e2)

