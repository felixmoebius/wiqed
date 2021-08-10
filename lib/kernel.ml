open Base
open Core
open Result.Let_syntax

let unfold context term args =
  let names = fst (List.unzip context) in
  let names_args = List.zip_exn names args in
  Term.subst_all names_args term

let rec normalize universe term =
  let open Term in
  match term with
  (* terminal *)
  | Box | Star | Free _ | Bound _ -> term
  (* normalize descendents *)
  | Lambda (typ, e) -> Lambda (normalize universe typ, normalize universe e)
  | Pi (typ, e) -> Pi (normalize universe typ, normalize universe e)
  (* beta reduction *)
  | App (f, x) -> (
      match normalize universe f with
      (* apply if we can... *)
      | Lambda (_, e) -> normalize universe (open0 e x)
      (* ...otherwise just return components *)
      | f' -> App (f', normalize universe x) )
  | Inst (name, args) ->
      (match Universe.find universe name with
      | Ok (Definition.Axiom _) -> Inst (name, List.map args ~f: (normalize universe))
      | Ok (Definition.Theorem (c, p, _)) -> normalize universe (unfold c p args)
      | Error e -> raise (Failure e)
      )

(* check for term equality by testing for alpha-conversion.
the locally-nameless approach makes this very easy, because
we only need to recursively check the structure of the terms
and ensure that free variable names and bound variable de Bruijn
indices match *)
let rec alpha_eq e1 e2 =
  let open Term in
  match (e1, e2) with
  (* terminal *)
  | Star, Star | Box, Box -> true
  (* matching de Bruijn indices *)
  | Bound i1, Bound i2 -> equal_int i1 i2
  (* matching free variable names *)
  | Free x1, Free x2 -> equal_string x1 x2
  (* equal iff descendents are equal *)
  | Lambda (l1, r1), Lambda (l2, r2)
  | Pi (l1, r1), Pi (l2, r2)
  | App (l1, r1), App (l2, r2) ->
      alpha_eq l1 l2 && alpha_eq r1 r2
  (* definition name matches and all args are equal *)
  | Inst (n1, a1), Inst (n2, a2) -> (
      List.(
        equal_string n1 n2
        &&
        match zip a1 a2 with
        | Unequal_lengths -> false
        | Ok z -> for_all z ~f:(fun (x1, x2) -> alpha_eq x1 x2)) )
  (* unequal in all other cases *)
  | _ -> false

(* check for beta-equality by checking the normalized term
for alpha-convertibility *)
(* let equal universe e1 e2 = alpha_eq (normalize universe e1) (normalize universe e2) *)

let check_arg_lengths (lu : Term.t list) lxa =
  let error = "arg length mismatch" in
  Result.ok_if_true List.(equal_int (length lu) (length lxa)) ~error

let _debug ctx exp d =
  Stdio.print_endline
    (String.concat
       [
         "(";
         Int.to_string d;
         ") ";
         String.concat
           (List.append
              (List.map (List.rev ctx) ~f:(fun (n, t) ->
                   String.concat [ "("; n; ": "; Term.string_of_exp t; "), " ]))
              [ " |- "; Term.string_of_exp exp ]);
       ])

let rec check_type (universe : Universe.t) (context : Context.t) (term : Term.t) (typ : Term.t) (depth : int) =
  let%bind t = Result.map (infer_type universe context term depth) ~f: (normalize universe) in
  let typ' = normalize universe typ in
  let error = sprintf "expected %s\nbut infered type is %s" (Term.string_of_exp typ') (Term.string_of_exp t) in
  alpha_eq t typ' |> Result.ok_if_true ~error

and infer_type (universe : Universe.t) (context : Context.t) (term : Term.t) (depth : int) =
  let open Term in
  (* _debug context term depth; *)

  match term with
  | Star -> rule_axiom_or_weak universe context term depth
  | Free x -> rule_var_or_weak universe context term depth x
  | Pi (a, b) -> rule_form universe context depth a b
  | App (m, n) -> rule_app universe context depth m n
  | Lambda (a, b) -> rule_abs universe context depth a b
  | Inst (name, args) -> rule_inst universe context depth name args
  | Box -> Error ("Box is not typeable at level (" ^ (Int.to_string depth) ^ ")")
  | Bound i ->
      Error
        (String.concat
           [ "bound variable "; Int.to_string i; " outside abstraction" ])

and rule_form universe context depth a b =
    (* ensure a is well-typed *)
    let%bind _ = infer_type universe context a (depth + 1) in

    (* open abstraction with fresh name *)
    let name = "@" ^ Int.to_string depth in
    let b' = Term.open0 b (Free name) in

    (* record 'name: a' in context an derive b : s,
        where s is also the type of the overall expression *)
    infer_type universe ((name, a) :: context) b' (depth + 1)

and rule_app universe context depth m n = 
    let%bind tm = infer_type universe context m (depth + 1) in
      (* TODO: I think tm has to be in weak head normal form
         or has to be fully normalized. *)
    match tm with
    | Pi (a, b) ->
        check_type universe context n a (depth + 1) >>= fun () ->
        Result.return (Term.open0 b a)
    | _ -> 
        Result.fail ("expected Pi abstraction at level (" ^ (Int.to_string depth) ^ ")")

and rule_abs universe context depth a b =
    let name = "@" ^ Int.to_string depth in
    (* open b *)
    let b_o = Term.open0 b (Free name) in

    (*  derive type of b' *)
    let%bind tb_o = infer_type universe ((name, a) :: context) b_o (depth + 1) in

    (* we opened b, thus replacing the variable that is bound by
        the abstraction with the fresh free variable 'name'.
        We derive b' : _B', but we are looking for b : _B.
        It follows that _B = (close0 _B name). *)
    let tb = Term.close0 tb_o name in
    let t = Term.Pi (a, tb) in

    (* derive (Pi _ : _A . _B) : s, we don't actually care
        about s, we only care that this typechecks *)
    let%bind _ = infer_type universe context t (depth + 1) in
    Result.return t

and rule_inst universe context depth name args =
    let%bind def = Universe.find universe name in
    let params = Definition.get_context def
    and typ = Definition.get_proposition def in
    let%bind () = check_arg_lengths args params in

    let lx, la = List.unzip params in
    let xu = List.zip_exn lx args in

    (* substitute A[U/X] *)
    let f i a = Term.subst_range i xu a in
    let ls = List.mapi la ~f in

    (* check U : S *)
    let f (u, s) = check_type universe context u s (depth + 1) in
    let%bind () = Utils.first_err (List.zip_exn args ls) ~f in

    (* return n[U/X] *)
    Result.return (Term.subst_all xu typ)

and rule_axiom_or_weak universe context term depth =
    match context with
    (* axiom, requires empty context. *)
    | [] -> Ok Term.Box
    (* context not empty. try weakening. *)
    | (_, _A) :: ctx' ->
        (* type check _A before discarding x: _A from ctx.
            try again with stronger context ctx'. *)
        infer_type universe ctx' _A (depth + 1) >>= fun _ ->
        infer_type universe ctx' term (depth + 1)

and rule_var_or_weak universe context term depth x =
    match context with
    (* cannot derive type_of x in empty ctx *)
    | [] -> Result.fail (String.concat [ "free var "; x; " not in context" ])
    (* ctx is not empty, but we don't know yet if x1 = x *)
    | (x1, _A) :: ctx' ->
        infer_type universe ctx' _A (depth + 1) >>= fun _ ->
        if equal_string x1 x (* if x1 == x, then x : _A *) then
          Result.return _A
          (* if x1 != x, then we perform weakening by discarding x1 : _A
              from the context. We already checked that _A is well-formed *)
        else infer_type universe ctx' term (depth + 1) 

let infer (universe : Universe.t) (context : Context.t) (term : Term.t) =
  infer_type universe context term 0

let check (universe : Universe.t) (context : Context.t) (term : Term.t) (typ : Term.t) =
  check_type universe context term typ 0

let infer_normalized (universe : Universe.t) (context : Context.t) (term : Term.t) =
  Result.map (infer universe context term) ~f: (normalize universe)
