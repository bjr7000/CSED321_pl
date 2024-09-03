(*
 * Call-by-value reduction   
 *)
exception NotImplemented 
exception Stuck

let freshVarCounter = ref 0
                          
(*   getFreshVariable : string -> string 
 *   use this function if you need to generate a fresh variable from s. 
 *)
let getFreshVariable s = 
  let _ = freshVarCounter := !freshVarCounter + 1
  in
  s ^ "__" ^ (string_of_int (!freshVarCounter))
               
(*
 * implement a single step with reduction using the call-by-value strategy.
 *)
let rec stepv e =
  let rec lfilter p l accl =
    match l with
    | [] -> accl
    | hd::tl -> if p(hd) then lfilter (p) (tl) (accl@(hd::[])) else lfilter (p) (tl) (accl)
  in
  let rec lfind l v =
    match l with
    | [] -> false
    | hd::tl -> if hd = v then true else lfind tl v
  in
  let rec fv e =
    match e with
    | Uml.Var v -> v::[] 
    | Uml.Lam (v, e) -> lfilter (fun x -> x!=v) (fv e) []
    | Uml.App (e1, e2) -> fv e1 @ fv e2 
  in
  let rec alpha used bound fresh exp =
    match exp with
    | Uml.Var v -> if lfind bound v then Uml.Var(v^fresh) else exp
    | Uml.Lam (v, e) -> if lfind used v then Uml.Lam(v^fresh, (alpha used (v::bound) fresh e)) else Uml.Lam(v, (alpha used bound fresh e))
    | Uml.App (e1, e2) -> Uml.App ((alpha used bound fresh e1),(alpha used bound fresh e2))
  in
  let rec subst arg var exp = (* [arg/var]exp*)
    match exp with
    | Uml.Var v -> if v = var then arg else exp
    | Uml.Lam (v, e) -> if v = var then exp else Uml.Lam (v, (subst arg var e))
    | Uml.App (e1, e2) -> Uml.App ((subst arg var e1),(subst arg var e2))
  in
  let beta arg var exp =
    subst arg var (alpha (fv arg) [] (getFreshVariable var) exp)
  in
  let rec stepv' n e =
    match e with
    | Uml.Var _ -> e
    | Uml.Lam (v1, e1) -> stepv e
    | Uml.App (e1, e2) -> 
        match e1, e2 with
        | Uml.App _, _ -> Uml.App((stepv' n e1),e2)
        | Uml.Lam (v1, e1'), Uml.App _ -> let e2' = stepv' 1 e2 in if e2 = e2' then beta e2 v1 e1' else Uml.App(e1, e2')
        | _, Uml.App _ -> if n = 0 then raise Stuck else Uml.App(e1, stepv' n e2)
        | Uml.Lam (v1, e1'), _ -> stepv e
        | _, _ -> if n = 0 then raise Stuck else Uml.App(e1, stepv' n e2)
  in
  match e with
  | Uml.Var _ -> raise Stuck
  | Uml.Lam (v1, e1) -> Uml.Lam (v1, stepv e1)
  | Uml.App (e1, e2) -> 
      match e1, e2 with
      | Uml.App _, _ -> Uml.App (stepv e1, e2) (* Lam *) (* e1 e2 -> e1' e2*)
      | Uml.Lam (v1, e1'), Uml.App _ -> let e2' = stepv' 1 e2 in if e2 = e2' then beta e2 v1 e1' else Uml.App(e1, e2') (* Arg *) (* e1 e2 -> e1 e2'*)
      | _, Uml.App _ -> Uml.App(e1, (stepv' 0 e2))
      | Uml.Lam (v1, e1'), _ -> beta e2 v1 e1' (* App *) (* (lam v1. e1) e2 -> [e2/v1]e1*)
      | _, _ -> raise Stuck


let stepOpt stepf e = try Some (stepf e) with Stuck -> None

let rec multiStep stepf e = try multiStep stepf (stepf e) with Stuck -> e

let stepStream stepf e =
  let rec steps e = 
    match (stepOpt stepf e) with 
      None -> Stream.from (fun _ -> None)
    | Some e' -> Stream.icons e' (steps e')
  in 
  Stream.icons e (steps e)

