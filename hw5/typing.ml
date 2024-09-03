open Tml

exception TypeError

(***************************************************** 
 * replace unit by your own type for typing contexts *
 *****************************************************)
type context = Tml.var -> Tml.tp

(*
 * For each function you introduce, 
 * write its type, specification, and invariant. 
 *)

let createEmptyContext () = fun x -> 
  match x with
  | _ -> raise TypeError

(* val typing : context -> Tml.exp -> Tml.tp *)
let rec typing cxt exp = 
  match exp with
  | Tml.Var v -> cxt v
  | Tml.Lam (v, tp, e) -> Tml.Fun (tp, (typing (fun x -> if x=v then tp else cxt x) e))
  | Tml.App (e1, e2) -> (match (typing cxt e1) with Tml.Fun (input,result) -> if input = (typing cxt e2) then result else raise TypeError | _ -> raise TypeError)
  | Tml.Pair (e1, e2) -> Tml.Prod ((typing cxt e1), (typing cxt e2))
  | Tml.Fst e -> (match (typing cxt e) with Tml.Prod (e1,_) -> e1 | _ -> raise TypeError)
  | Tml.Snd e -> (match (typing cxt e) with Tml.Prod (_,e2) -> e2 | _ -> raise TypeError)
  | Tml.Eunit -> Tml.Unit
  | Tml.Inl (e, tp) -> Tml.Sum ((typing cxt e), tp)
  | Tml.Inr (e, tp) -> Tml.Sum (tp, (typing cxt e))
  | Tml.Case (e, x1, e1, x2, e2) -> 
        (match (typing cxt e) with 
          | Tml.Sum (tp1,tp2) -> if (typing cxt (Tml.Lam (x1, tp1, e1))) = (typing cxt (Tml.Lam (x2, tp2, e2))) then (typing cxt (Tml.Lam (x1, tp1, e1))) else raise TypeError
          | _ -> raise TypeError)
  | Tml.Fix (v, tp, e) -> if (typing cxt (Tml.Lam (v, tp, e))) = Tml.Fun(tp, tp) then tp else raise TypeError
  | Tml.True -> Tml.Bool
  | Tml.False -> Tml.Bool
  | Tml.Ifthenelse (e, e1, e2) -> if (typing cxt e) = Tml.Bool && (typing cxt e1) = (typing cxt e2) then (typing cxt e1) else raise TypeError
  | Tml.Num _ -> Tml.Int
  | Tml.Plus -> Tml.Fun ((Tml.Prod (Tml.Int, Tml.Int), Tml.Int))
  | Tml.Minus -> Tml.Fun ((Tml.Prod (Tml.Int, Tml.Int), Tml.Int))
  | Tml.Eq -> Tml.Fun ((Tml.Prod (Tml.Int, Tml.Int), Tml.Bool))

let typeOf e = typing (createEmptyContext ()) e 
let typeOpt e = try Some (typeOf e) 
                with TypeError -> None



