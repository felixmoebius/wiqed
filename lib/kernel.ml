open Base
open Core
open Result.Let_syntax


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
  let error = "type mismatch" in
  let%bind t = infer_type universe context term depth in
  Term.beta_eq t typ |> Result.ok_if_true ~error

and infer_type (universe : Universe.t) (context : Context.t) (term : Term.t) (depth : int) =
  let open Term in
  (* _debug context term depth; *)

  let rule_form a b =
    (* ensure a is well-typed *)
    let%bind _ = infer_type universe context a (depth + 1) in

    (* open abstraction with fresh name *)
    let name = "@" ^ Int.to_string depth in
    let b' = open0 b (Free name) in

    (* record 'name: a' in context an derive b : s,
        where s is also the type of the overall expression *)
    infer_type universe ((name, a) :: context) b' (depth + 1)
  in

  let rule_app m n = 
    let%bind tm = infer_type universe context m (depth + 1) in
      (* TODO: i think tm has to be in weak head normal form
         or has to be fully normalized. *)
    match tm with
    | Pi (a, b) ->
        check_type universe context n a (depth + 1) >>= fun () ->
        Result.return (open0 b a)
    | _ -> 
        Result.fail ("expected Pi abstraction at level (" ^ (Int.to_string depth) ^ ")")
  in

  let rule_abs a b =
    let name = "@" ^ Int.to_string depth in
    (* open b *)
    let b_o = open0 b (Free name) in

    (*  derive type of b' *)
    let%bind tb_o = infer_type universe ((name, a) :: context) b_o (depth + 1) in

    (* we opened b, thus replacing the variable that is bound by
        the abstraction with the fresh free variable 'name'.
        We derive b' : _B', but we are looking for b : _B.
        It follows that _B = (close0 _B name). *)
    let tb = close0 tb_o name in
    let t = Pi (a, tb) in

    (* derive (Pi _ : _A . _B) : s, we don't actually care
        about s, we only care that this typechecks *)
    let%bind _ = infer_type universe context t (depth + 1) in
    Result.return t
  in

  (* let rule_inst_fact fact arguments =
    let ctx = Fact.get_context fact
    and typ = Fact.get_type fact in

    let%bind () = check_arg_lengths arguments ctx in

    let lx, la = List.unzip ctx in
    let xu = List.zip_exn lx arguments in

    (* substitute A[U/X] *)
    let f i a = Term.subst_range i xu a in
    let ls = List.mapi la ~f in

    (* check U : S *)
    let f (u, s) = check_type universe context u s (depth + 1) in
    let%bind () = Utils.first_err (List.zip_exn arguments ls) ~f in

    (* return n[U/X] *)
    Result.return (Term.subst_all xu typ)
  in *)

  let instantiate ctx typ args =
    let%bind () = check_arg_lengths args ctx in

    let lx, la = List.unzip ctx in
    let xu = List.zip_exn lx args in

    (* substitute A[U/X] *)
    let f i a = Term.subst_range i xu a in
    let ls = List.mapi la ~f in

    (* check U : S *)
    let f (u, s) = check_type universe context u s (depth + 1) in
    let%bind () = Utils.first_err (List.zip_exn args ls) ~f in

    (* return n[U/X] *)
    Result.return (Term.subst_all xu typ)
  in

  let rule_inst name args =
    match Universe.find universe name with
    | `Axiom a -> 
        instantiate (Axiom.get_context a) (Axiom.get_proposition a) args
    | `Theorem t -> 
        instantiate (Theorem.get_context t) (Theorem.get_proposition t) args
    | `Definition d -> Definition.instantiate d args
    | `Not_found -> Result.fail (sprintf "unknown symbol %s" name)
  in

  let rule_axiom_or_weak () =
    match context with
    (* axiom, requires empty context. *)
    | [] -> Ok Box
    (* context not empty. try weakening. *)
    | (_, _A) :: ctx' ->
        (* type check _A before discarding x: _A from ctx.
            try again with stronger context ctx'. *)
        infer_type universe ctx' _A (depth + 1) >>= fun _ ->
        infer_type universe ctx' term (depth + 1)
  in

  let rule_var_or_weak x =
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
  in
  
  (* _debug ctx term depth; *)
  match term with
  | Star -> rule_axiom_or_weak ()
  | Free x -> rule_var_or_weak x
  | Pi (a, b) -> rule_form a b
  | App (m, n) -> rule_app m n
  | Lambda (a, b) -> rule_abs a b
  | Inst (name, args) -> rule_inst name args
  | Box -> Error ("Box is not typeable at level (" ^ (Int.to_string depth) ^ ")")
  | Bound i ->
      Error
        (String.concat
           [ "bound variable "; Int.to_string i; " outside abstraction" ])

let infer (universe : Universe.t) (context : Context.t) (term : Term.t) =
  infer_type universe context term 0

let check (universe : Universe.t) (context : Context.t) (term : Term.t) (typ : Term.t) =
  check_type universe context term typ 0

let infer_normalized (universe : Universe.t) (context : Context.t) (term : Term.t) =
  Result.map (infer universe context term) ~f: Term.normalize
