open Base
(* open Result.Monad_infix *)
open Result.Let_syntax

type ctx = (string * Term.t) list
type def = {
  name: string;
  args: (string * Term.t) list;
  term: Term.t option;
  typ': Term.t;
}
type env = def list

let env_find (env : env) s = 
  let r = (List.find env ~f: (fun d -> equal_string s d.name)) in
    Result.of_option r ~error: (s ^ " not in env")

let first_err l ~f =
  let rec loop = function
  | [] -> Result.return ()
  | x :: l' -> (f x) >>= fun _ -> loop l'
  in loop l

let subst_all (xu : (string * Term.t) list) (a : Term.t) =
  List.fold xu ~init: a ~f: (fun a' (x, u) -> Term.subst a' x u)

let subst_range i xu a = subst_all (List.take xu i) a

let check_arg_lengths (lu : Term.t list) lxa =
  let error = "arg length mismatch" in
  Result.ok_if_true List.(equal_int (length lu) (length lxa)) ~error

let _debug ctx exp d =
  Stdio.print_endline 
  (String.concat [
    "("; Int.to_string d; ") ";
    (String.concat
      (List.append
        (List.map (List.rev ctx) ~f: (fun (n, t) 
         -> String.concat ["("; n; ": "; Term.string_of_exp t; "), "]))
        [" |- "; Term.string_of_exp exp]
      )
  )])

let rec type_of' env ctx exp d =
  let open Term in
  (* _debug ctx exp d; *)
  match exp with

  (* '*' *)
  | Star -> 
    (match ctx with
    (* axiom, requires empty context. *)
    | [] -> Ok(Box)
    (* context not empty. try weakening. *)
    | (_, _A) :: ctx' ->
      (* type check _A before discarding x: _A from ctx.
      try again with stronger context ctx'. *)
      type_of' env ctx' _A  (d+1) >>= fun _ ->
      type_of' env ctx' exp (d+1)
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
  let%bind t = type_of' env ctx u d in Term.beta_eq t s 
  |> Result.ok_if_true ~error

let type_of ctx exp = type_of' [] ctx exp 0
  
let check ctx exp typ = (function 
  | Error(_) -> false 
  | Ok(t) -> Term.beta_eq typ t
  ) (type_of ctx exp)

let normalized_type_of ctx exp =
  Result.Monad_infix.(
    type_of ctx exp >>= (fun x -> Ok(Term.normalize x))
  )