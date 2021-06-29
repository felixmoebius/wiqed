open Base
(* open Result.Monad_infix *)
open Result.Let_syntax

type id = string

type exp =
  | Box
  | Star
  | Free   of id
  | Bound  of int
  | Lambda of exp * exp
  | Pi     of exp * exp
  | App    of exp * exp
  | Def    of string * (exp list)

type ctx = (id * exp) list
type def = {
  name: string;
  args: (string * exp) list;
  term: exp option;
  typ': exp;
}
type env = def list

let rec string_of_exp exp = 
  let open String in
  match exp with
  | Box          -> "Box"
  | Star         -> "*"
  | Free(id)     -> id
  | Bound(i)     -> Int.to_string i
  | Lambda(t, e) -> 
    concat ["(lambda "; string_of_exp t; " . "; string_of_exp e; ")"]
  | Pi(t, e)     ->
    concat ["(Pi "; string_of_exp t; " . "; string_of_exp e; ")"]
  | App(l, r)    ->
    concat ["("; string_of_exp l; " "; string_of_exp r; ")"]
  | Def(n, _)       -> n

let rec _open exp k u = match exp with
  | Box | Star | Free(_) -> exp
  | Bound(i)      -> if equal i k then u else exp
  | App(t1, t2)   -> App(_open t1 k u, _open t2 k u)
  | Lambda(_T, e) -> Lambda(_open _T k u, _open e (k + 1) u)
  | Pi(_T, e)     -> Pi(_open _T k u, _open e (k + 1) u)
  | Def(n, a)     -> 
    Def(n, List.map a ~f: (fun e -> _open e k u))

let open0 e u = _open e 0 u

let rec _close exp k x = match exp with
  | Box | Star | Bound(_) -> exp
  | Free(x')      -> if String.equal x x' then Bound(k) else exp
  | App(t1, t2)   -> App(_close t1 k x, _close t2 k x)
  | Lambda(_T, e) -> Lambda(_close _T k x, _close e (k + 1) x)
  | Pi(_T, e)     -> Pi(_close _T k x, _close e (k + 1) x)
  | Def(n, a)     -> 
    Def(n, List.map a ~f: (fun e -> _close e k x))

let close0 e x = _close e 0 x

let rec normalize exp = match exp with
  (* atom *)
  | Box | Star | Free(_) | Bound(_) -> exp

  (* normalize descendents *)
  | Lambda(_T, e) -> Lambda(normalize _T, normalize e)
  | Pi(_T, e) -> Pi(normalize _T, normalize e)

  (* beta reduction *)
  | App(f, x) ->
    (match normalize f with
    | Lambda(_T, e) -> normalize (open0 e x)
    | f' -> App(f', normalize x))

  | Def(_) -> raise (Failure "unfold unimplemented")

let rec subst e z u = match e with
  | Box | Star | Bound(_) -> e
  | Free(z') -> if equal_string z z' then u else e
  | App(t1, t2) -> App(subst t1 z u, subst t2 z u)
  | Lambda(_T, e') -> Lambda(subst _T z u, subst e' z u)
  | Pi(_T, e') -> Pi(subst _T z u, subst e' z u)
  | Def(n, a) ->
    Def(n, List.map a ~f: (fun e' -> subst e' z u))

let rec alpha_eq e1 e2 = match e1, e2 with
  (* atom *)
  | (Star, Star) | (Box, Box) -> true

  (* matching de Bruijn indeces *)
  | (Bound(i1), Bound(i2)) -> equal_int i1 i2

  (* matching identifiers *)
  | (Free(x1), Free(x2)) -> equal_string x1 x2

  (* equal iff descendents are equal *)
  | (Lambda(_T1, e1'), Lambda(_T2, e2'))
  | (Pi(_T1, e1'), Pi(_T2, e2')) -> 
    (alpha_eq _T1 _T2) && (alpha_eq e1' e2')
  | (App(f1, x1), App(f2, x2)) ->
    (alpha_eq f1 f2) && (alpha_eq x1 x2)

  | (Def(n1, a1), Def(n2, a2)) ->
    List.(
    equal_string n1 n2 && (match (zip a1 a2) with
    | Unequal_lengths -> false
    | Ok(z) ->  for_all z ~f: (fun (x1, x2) -> alpha_eq x1 x2))
    )

  | _ -> false

let beta_eq e1 e2 = alpha_eq (normalize e1) (normalize e2)

let env_find (env : env) s = 
  let r = (List.find env ~f: (fun d -> equal_string s d.name)) in
    Result.of_option r ~error: (s ^ " not in env")

let first_err l ~f =
  let rec loop = function
  | [] -> Result.return ()
  | x :: l' -> (f x) >>= fun _ -> loop l'
  in loop l

let subst_all (xu : (string * exp) list) (a : exp) =
  List.fold xu ~init: a ~f: (fun a' (x, u) -> subst a' x u)

let subst_range i xu a = subst_all (List.take xu i) a

let check_arg_lengths (lu : exp list) lxa =
  let error = "arg length mismatch" in
  Result.ok_if_true List.(equal_int (length lu) (length lxa)) ~error

let _debug ctx exp d =
  Stdio.print_endline 
  (String.concat [
    "("; Int.to_string d; ") ";
    (String.concat
      (List.append
        (List.map (List.rev ctx) ~f: (fun (n, t) 
         -> String.concat ["("; n; ": "; string_of_exp t; "), "]))
        [" |- "; string_of_exp exp]
      )
  )])

let rec type_of' (env : env) ctx exp d = 

  (* _debug ctx exp d; *)
  match exp with
  | Star -> (match ctx with
    (* axiom *)
    | [] -> Ok(Box)

    (* need empty context, so try weakening *)
    | (_, _A) :: ctx' ->
      (* type check _A before discarding x: _A from ctx
      try again with stronger context ctx' *)
      type_of' env ctx' _A (d+1) >>= fun _ -> type_of' env ctx' exp (d+1)
    )

  (* 'x' *)
  | Free(x) -> 
    (match ctx with
    (* cannot derive type_of x in empty ctx *)
    | [] -> Result.fail (String.concat ["free var "; x; " not in context"])

    (* ctx is not empty, but we don't know yet if x1 = x *)
    | (x1, _A) :: ctx' ->
      type_of' env ctx' _A (d+1) >>= fun _ ->
      if equal_string x1 x
      (* if x1 == x, then x : _A *)
      then Result.return _A
      (* if x1 != x, then we perform weakening by discarding x1 : _A 
      from the context. We already checked that _A is well-formed *)
      else type_of' env ctx' exp (d+1)
    )
    
  (* Pi _ : _A . _B *)
  | Pi(_A, _B) ->
    (* ensure _A is well-typed *)
    let%bind _ = type_of' env ctx _A (d+1) in

    (* open abstraction with fresh name *)
    let name = "@" ^ Int.to_string d in
    let _B' = open0 _B (Free(name)) in

    (* record 'name: _A' in context an derive _B : s,
    where s is also the type of the overall expression *)
    type_of' env ((name, _A) :: ctx) _B' (d+1)

  (* m n *)
  | App(m, n) ->
    let%bind tm = type_of' env ctx m (d+1) in
    (* TODO: i think tm has to be in weak head normal form
    or has to be fully normalized. *)
    (match tm with
    | Pi(_A, _B) -> 
      check env ctx (d+1) n _A >>= fun () ->
      Result.return (open0 _B _A)
    | _ -> 
      Result.fail "expected Pi abstraction"
    )

  (* lambda _ : _A . b *)
  | Lambda(_A, b) ->
    let name = "@" ^ Int.to_string d in
    (* open b *)
    let b' = open0 b (Free name) in

    (*  derive type of b' *)
    let%bind _B' = type_of' env ((name, _A) :: ctx) b' (d+1) in

    (* we opened b, thus replacing the variable that is bound by
    the abstraction with the fresh free variable 'name'.
    We derive b' : _B', but we are looking for b : _B.
    It follows that _B = (close0 _B name). *)
    let _B = close0 _B' name in
    let t = Pi(_A, _B) in

    (* derive (Pi _ : _A . _B) : s, we don't actually care
    about s, we only care that this typechecks *)
    let%bind _ = type_of' env ctx t (d+1) in
    Result.return t

  | Def(n, lu) ->
    (* lookup definition *)
    let%bind def = env_find env n in
    let%bind ()  = check_arg_lengths lu def.args in
    
    let (lx, la) = List.unzip def.args in
    let xu       = List.zip_exn lx lu in

    (* substitute A[U/X] *)
    let f i a = subst_range i xu a in
    let ls = List.mapi la ~f in

    (* check U : S *)
    let f (u, s) = check env ctx (d+1) u s in
    let%bind ()  = first_err (List.zip_exn lu ls) ~f in

    (* return n[U/X] *)
    Result.return (subst_all xu def.typ')

    
  | Box      -> Error("Box is not typeable")
  | Bound(i) -> Error(String.concat 
    ["bound variable "; Int.to_string i; " outside abstraction"])

and check env ctx d u s =
  let error = "type mismatch" in
  let%bind t = type_of' env ctx u d in beta_eq t s 
  |> Result.ok_if_true ~error

let type_of ctx exp = type_of' [] ctx exp 0
  
let check ctx exp typ = (function 
  | Error(_) -> false 
  | Ok(t) -> beta_eq typ t
  ) (type_of ctx exp)

let normalized_type_of ctx exp =
  Result.Monad_infix.(
    type_of ctx exp >>= (fun x -> Ok(normalize x))
  )