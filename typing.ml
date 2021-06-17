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
        concat ["("; string_of_exp l; string_of_exp r; ")"]

let rec _open exp k u = match exp with
    | Box | Star | Free(_) -> exp
    | Bound(i) -> if equal i k then u else exp
    | App(f, x) -> App(_open f k u, _open x k u)
    | Lambda(_T, e) -> Lambda(_open _T k u, _open e (k + 1) u)
    | Pi(_T, e) -> Pi(_open _T k u, _open e (k + 1) u)

let open0 e u = _open e 0 u

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

let fresh_name _ = "x"

let rec type_of ctx exp = 
    let open Result.Monad_infix in
    match exp with
    | Star -> (match ctx with
        (* axiom *)
        | [] -> Ok(Box)

        (* need empty context, so try weakening *)
        | (_, _A) :: ctx' ->
            (* type check _A before discarding x: _A from ctx
            try again with stronger context ctx' *)
            type_of ctx' _A >>= fun _ -> type_of ctx' exp
        )

    | Free(x') -> (match ctx with
        (* cannot derive type_of x' in empty ctx *)
        | [] -> Error(String.concat ["free var "; x';" not in context"])

        (* x' needs to be recorded in ctx *)
        | (x, _A) :: ctx' ->
            let tA = type_of ctx' _A in
            match tA with 
            | Ok(_) -> if equal_string x x' then Ok _A else type_of ctx' exp
            | _ -> tA
        )
        
    | Pi(_A, _B) ->
        (* ensure _A is well-typed *)
        type_of ctx _A >>= fun _ ->

            (* open abstraction with fresh name *)
            let name = fresh_name ctx in
            let _B' = open0 _B (Free(name)) in

            (* record 'name: _A' in context an check _B *)
            type_of ((name, _A) :: ctx) _B'


    (* appl *)
    | App(m, n) ->
        type_of ctx m >>= (function
            | Pi(_A, _B) -> 
                type_of ctx n >>= (fun _A' ->
                    if not (beta_eq _A _A') then Error("")
                    else Ok(open0 _B _A))
            | _ -> 
                Error("expected Pi abstraction"))

    | Lambda(_A, b) ->
        let name = fresh_name ctx in
        (match type_of ((name, _A) :: ctx) (open0 b (Free(name))) with
        | Error(e) -> Error e
        |   Ok(_B) ->
            (match type_of ctx (Pi(_A, _B)) with
            | Error(e) -> Error(e)
            |    Ok(_) -> Ok(Pi(_A, _B))
            )
        )

    | Box -> Error("Box is not typeable")
    | _ -> Error("")
    
let check ctx exp typ = (function 
    | Error(_) -> false 
    | Ok(t) -> beta_eq typ t
    ) (type_of ctx exp)

let normalized_type_of ctx exp =
    Result.Monad_infix.(
        type_of ctx exp >>= (fun x -> Ok(normalize x))
    )