open Base

type id = string

type exp =
    | Box
    | Star
    | Free   of id
    | Bound  of int
    | Lambda of exp * exp
    | Pi     of exp * exp
    | App    of exp * exp

type ctx = (id * exp) list

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

let rec _open exp k u = match exp with
    | Box | Star | Free(_) -> exp
    | Bound(i)      -> if equal i k then u else exp
    | App(t1, t2)   -> App(_open t1 k u, _open t2 k u)
    | Lambda(_T, e) -> Lambda(_open _T k u, _open e (k + 1) u)
    | Pi(_T, e)     -> Pi(_open _T k u, _open e (k + 1) u)

let open0 e u = _open e 0 u

let rec _close exp k x = match exp with
    | Box | Star | Bound(_) -> exp
    | Free(x')      -> if String.equal x x' then Bound(k) else exp
    | App(t1, t2)   -> App(_close t1 k x, _close t2 k x)
    | Lambda(_T, e) -> Lambda(_close _T k x, _close e (k + 1) x)
    | Pi(_T, e)     -> Pi(_close _T k x, _close e (k + 1) x)

let close0 e x = _close e 0 x

let rec normalize exp = match exp with
    (* atom *)
    | Box | Star | Free(_) | Bound(_) -> exp

    (* normalize descendents *)
    | Lambda(_T, e) -> Lambda(normalize _T, normalize e)
    | Pi(_T, e) -> Pi(normalize _T, normalize e)

    (* beta reduction *)
    | App(f, x) ->
        match normalize f with
        | Lambda(_T, e) -> normalize (open0 e x)
        | f' -> App(f', normalize x)

let rec alpha_eq e1 e2 = match e1, e2 with
    (* atom *)
    | (Star, Star) | (Box, Box) -> true

    (* matching de Bruijn indeces *)
    | (Bound(i1), Bound(i2)) -> equal i1 i2

    (* matching identifiers *)
    | (Free(x1), Free(x2)) -> equal_string x1 x2

    (* equal iff descendents are equal *)
    | (Lambda(_T1, e1'), Lambda(_T2, e2'))
    | (Pi(_T1, e1'), Pi(_T2, e2')) -> 
        (alpha_eq _T1 _T2) && (alpha_eq e1' e2')
    | (App(f1, x1), App(f2, x2)) ->
        (alpha_eq f1 f2) && (alpha_eq x1 x2)
    | _ -> false

let beta_eq e1 e2 = alpha_eq (normalize e1) (normalize e2)

(* let fresh_counter = ref 1
let fresh_name () =
	let i = !fresh_counter in fresh_counter := i + 1;
	let i = Int.to_string i in "@" ^ i *)



let rec type_of' ctx exp d = 
    let open Result.Monad_infix in
    (* Stdio.print_endline 
    (String.concat [
        "("; Int.to_string d; ") ";
        (String.concat
            (List.append
                (List.map (List.rev ctx) ~f: (fun (n, t) 
                 -> String.concat ["("; n; ": "; string_of_exp t; "), "]))
                [" |- "; string_of_exp exp]
            )
    )]); *)
    match exp with
    | Star -> (match ctx with
        (* axiom *)
        | [] -> Ok(Box)

        (* need empty context, so try weakening *)
        | (_, _A) :: ctx' ->
            (* type check _A before discarding x: _A from ctx
            try again with stronger context ctx' *)
            type_of' ctx' _A (d+1) >>= fun _ -> type_of' ctx' exp (d+1)
        )

    | Free(x') -> (match ctx with
        (* cannot derive type_of x' in empty ctx *)
        | [] -> Error(String.concat ["free var "; x';" not in context"])

        (* x' needs to be recorded in ctx *)
        | (x, _A) :: ctx' ->
            let tA = type_of' ctx' _A (d+1) in
            match tA with 
            | Ok(_) -> if equal_string x x' then Ok _A else type_of' ctx' exp (d+1)
            | _ -> tA
        )
        
    | Pi(_A, _B) ->
        (* ensure _A is well-typed *)
        type_of' ctx _A (d+1) >>= fun _ ->

            (* open abstraction with fresh name *)
            let name = "@" ^ Int.to_string d in
            let _B' = open0 _B (Free(name)) in

            (* record 'name: _A' in context an check _B *)
            type_of' ((name, _A) :: ctx) _B' (d+1)


    (* appl *)
    | App(m, n) ->
        type_of' ctx m (d+1) >>= (function
            | Pi(_A, _B) -> 
                type_of' ctx n (d+1) >>= (fun _A' ->
                    if not (beta_eq _A _A') then 
                        Error("type mismatch in application")
                    else Ok(open0 _B _A))
            | _ -> 
                Error("expected Pi abstraction"))

    | Lambda(_A, b) ->
        let name = "@" ^ Int.to_string d in
        (match type_of' ((name, _A) :: ctx) (open0 b (Free(name))) (d+1) with
        | Error(e) -> Error e
        |   Ok(_B) ->
            let t = Pi((close0 _A name), (close0 _B name)) in
            (match type_of' ctx t (d+1) with
            | Error(e) -> Error(e)
            |    Ok(_) -> Ok(t)
            )
        )

    | Box      -> Error("Box is not typeable")
    | Bound(i) -> Error(String.concat 
        ["bound variable "; Int.to_string i; " outside abstraction"])

let type_of ctx exp = type_of' ctx exp 0
    
let check ctx exp typ = (function 
    | Error(_) -> false 
    | Ok(t) -> beta_eq typ t
    ) (type_of ctx exp)

let normalized_type_of ctx exp =
    Result.Monad_infix.(
        type_of ctx exp >>= (fun x -> Ok(normalize x))
    )