open Tml
exception NotImplemented 
exception Stuck
exception NotConvertible

type stoval = 
    Computed of value 
  | Delayed of exp * env

 and stack =
   Hole_SK
   | Frame_SK of stack * frame

 and state =
   Anal_ST of (stoval Heap.heap) * stack * exp * env
   | Return_ST of (stoval Heap.heap) * stack * value 

 (* Define your own datatypes *)
 and env = exp -> int

 and value = 
  | Indv of index 
  | Lamv of exp 
  | Appv of exp * exp
  | Pairv of exp * exp
  | Fstv of exp 
  | Sndv of exp 
  | Eunitv 
  | Inlv of exp 
  | Inrv of exp 
  | Casev of exp * exp * exp
  | Truev 
  | Falsev
  | Ifthenelsev of exp * exp * exp
  | Numv of int 
  | Plusv 
  | Minusv 
  | Eqv

 and frame = Hole_Fr | Value_Fr of value | Exp_Fr of exp
  | Lam_Fr of frame
  | App_Fr of frame * exp
  | App'_Fr of exp * frame
  | Pair_Fr of frame * exp
  | Pair'_Fr of exp * frame
  | Fst_Fr of frame
  | Snd_Fr of frame
  | Inl_Fr of frame
  | Inr_Fr of frame
  | Case_Fr of frame * exp * exp
  | Ifthenelse_Fr of frame * exp * exp
  | Fix_Fr of frame

(* Define your own empty environment *)
let emptyEnv = fun exp -> 0

(* Implement the function value2exp : value -> Tml.exp
 * Warning : If you give wrong implementation of this function,
 *           you wiil receive no credit for the entire third part!  *)
let value2exp value' =
  match value' with
  | Indv (index) -> Ind (index) 
  | Lamv (exp) -> Lam (exp) 
  | Appv (exp1, exp2) -> App (exp1, exp2)
  | Pairv (exp1, exp2) -> Pair (exp1, exp2)
  | Fstv (exp) -> Fst (exp) 
  | Sndv (exp) -> Snd (exp) 
  | Eunitv -> Eunit
  | Inlv (exp) -> Inl (exp) 
  | Inrv (exp) -> Inr (exp) 
  | Casev (exp1, exp2, exp3) -> Case (exp1, exp2, exp3)
  | Truev -> True
  | Falsev -> False
  | Ifthenelsev (exp1, exp2, exp3) -> Ifthenelse (exp1, exp2, exp3)
  | Numv (int) -> Num (int)
  | Plusv -> Plus
  | Minusv -> Minus
  | Eqv -> Eq

(* Problem 1. 
 * texp2exp : Tml.texp -> Tml.exp *)
let texp2exp tex =
  let rec fnconv tex fn =
    match tex with
    | Tvar var -> fun x -> if fn x < fn "_" || x = var then fn x else if fn var = fn "_" then (fn x)+1 else fn x
    | Tlam (var, tp, texp) -> 
      fun x ->if fn x < fn "_" then fn x
              else if x = var then (fnconv texp (fun x -> if x = var then -1 else fn x)) "_"
              else ((fnconv texp (fun x -> if x = var then -1 else fn x)) x)
    | Tapp (texp1, texp2) -> fnconv texp1 (fnconv texp2 fn)
    | Tpair (texp1, texp2) -> fnconv texp1 (fnconv texp2 fn)
    | Tfst texp -> fnconv texp fn
    | Tsnd texp -> fnconv texp fn
    | Tinl (texp,tp) -> fnconv texp fn
    | Tinr (texp,tp) -> fnconv texp fn
    | Tcase (texp,var1,texp1,var2,texp2) -> fnconv texp (fnconv (Tlam (var1, Int, texp1)) (fnconv (Tlam (var2, Int, texp2)) fn))
    | Tfix (var, tp, texp) -> 
      fun x ->if fn x < fn "_" then fn x
              else if x = var then (fnconv texp (fun x -> if x = var then -1 else fn x)) "_"
              else ((fnconv texp (fun x -> if x = var then -1 else fn x)) x)
    | Tifthenelse (texp1,texp2,texp3) -> fnconv texp1 (fnconv texp2 (fnconv texp3 fn))
    | _ -> fn
    in
  let rec texp2exp' tex fn = 
    match tex with
    | Tvar var -> Ind (fn var)
    | Tlam (var, tp, texp) -> Lam (texp2exp' texp (fun x -> if x = var then 0 else (fn x)+1))
    | Tapp (texp1, texp2) -> App (texp2exp' texp1 (fnconv texp2 fn), texp2exp' texp2 fn)
    | Tpair (texp1, texp2) -> Pair (texp2exp' texp1 (fnconv texp2 fn), texp2exp' texp2 fn)
    | Tfst texp -> Fst (texp2exp' texp fn)
    | Tsnd texp -> Snd (texp2exp' texp fn)
    | Teunit -> Eunit
    | Tinl (texp,tp) -> Inl (texp2exp' texp fn)
    | Tinr (texp,tp) -> Inr (texp2exp' texp fn)
    | Tcase (texp,var1,texp1,var2,texp2) -> Case(texp2exp' texp (fnconv (Tlam (var1, Int, texp1)) (fnconv (Tlam (var2, Int, texp2)) fn)),
                                                 texp2exp' texp1 (fun x -> if x = var1 then 0 else ((fnconv (Tlam (var2, Int, texp2)) fn) x)+1), 
                                                 texp2exp' texp2 (fun x -> if x = var2 then 0 else (fn x)+1))
    | Tfix (var, tp, texp) -> Fix (texp2exp' texp (fun x -> if x = var then 0 else (fn x)+1))
    | Ttrue -> True
    | Tfalse -> False
    | Tifthenelse (texp1,texp2,texp3) -> Ifthenelse (texp2exp' texp1 (fnconv texp2 (fnconv texp3 fn)), texp2exp' texp2 (fnconv texp3 fn), texp2exp' texp3 fn)
    | Tnum i -> Num (i)
    | Tplus -> Plus
    | Tminus -> Minus
    | Teq -> Eq
    in
  texp2exp' tex (fun x -> 0)

(* Problem 2. 
 * step1 : Tml.exp -> Tml.exp *)   
let rec step1 exp' =
  let rec isitvalue exp =
    match exp with
    | Ind _ -> true
    | Lam _ -> true
    | App (exp1, exp2) -> begin match exp1, exp2 with 
      | Lam _, _ -> false
      | Fst _, Pair _ -> false
      | Snd _, Pair _ -> false
      | Plus, Pair (Num _, Num _) -> false 
      | Minus, Pair (Num _, Num _) -> false 
      | Eq, Pair (Num _, Num _) -> false 
      | _, _ -> isitvalue exp1 && isitvalue exp2 
    end
    | Pair (exp1, exp2) -> isitvalue exp1 && isitvalue exp2
    | Fst (exp) -> isitvalue exp
    | Snd (exp) -> isitvalue exp
    | Eunit -> true
    | Inl (exp) -> isitvalue exp
    | Inr (exp) -> isitvalue exp
    | Case (exp, exp1, exp2) -> if isitvalue exp then begin match exp with Inl _ -> false | Inr _ -> false | _ -> true end else false
    | Fix _ -> false
    | True -> true
    | False -> true
    | Ifthenelse (tf, exp1, exp2) -> if isitvalue tf then begin match exp with True -> false | False -> false | _ -> true end else false
    | Num _ -> true
    | Plus -> true
    | Minus -> true
    | Eq -> true
  in
  let rec subst exp' var num = 
    let rec shift var num bound = 
      match var with
      | Ind (index) -> if index < bound then Ind(index) else Ind(index + num)
      | Lam (exp) -> Lam (shift exp num (bound+1))
      | App (exp1, exp2) -> App (shift exp1 num bound, shift exp2 num bound)
      | Pair (exp1, exp2) -> Pair (shift exp1 num bound, shift exp2 num bound)
      | Fst (exp) -> Fst (shift exp num bound)
      | Snd (exp) -> Snd (shift exp num bound)
      | Eunit -> Eunit
      | Inl (exp) -> Inl (shift exp num bound)
      | Inr (exp) -> Inr (shift exp num bound)
      | Case (exp, exp1, exp2) -> Case (shift exp num bound, shift exp1 num bound, shift exp2 num bound)
      | Fix (exp) -> Fix (shift exp num (bound+1))
      | True -> True
      | False -> False
      | Ifthenelse (tf, exp1, exp2) -> Ifthenelse (shift tf num bound, shift exp1 num bound, shift exp2 num bound)
      | Num (int) -> Num (int) 
      | Plus -> Plus
      | Minus -> Minus
      | Eq -> Eq
    in
    match exp' with
    | Ind (index) -> if index < num then Ind(index) else if index = num then shift var num 0 else Ind (index-1)
    | Lam (exp) -> Lam (subst exp var (num+1))
    | App (exp1, exp2) -> App (subst exp1 var num, subst exp2 var num)
    | Pair (exp1, exp2) -> Pair (subst exp1 var num, subst exp2 var num)
    | Fst (exp) -> Fst (subst exp var num)
    | Snd (exp) -> Snd (subst exp var num)
    | Eunit -> Eunit
    | Inl (exp) -> Inl (subst exp var num)
    | Inr (exp) -> Inr (subst exp var num)
    | Case (exp, exp1, exp2) -> Case (subst exp var num, subst exp1 var num, subst exp2 var num)
    | Fix (exp) -> Fix (subst exp var (num+1))
    | True -> True
    | False -> False
    | Ifthenelse (tf, exp1, exp2) -> Ifthenelse (subst tf var num, subst exp1 var num, subst exp2 var num)
    | Num (int) -> Num (int) 
    | Plus -> Plus
    | Minus -> Minus
    | Eq -> Eq
  in
  match exp' with
  | Ind (index) -> raise Stuck
  | Lam (exp) -> Lam (step1 exp)
  | App (exp1, exp2) -> if isitvalue exp1 then begin match exp1, exp2 with
    | Plus, Pair (Num(i1), Num(i2)) -> Num(i1+i2) (* Plus *)
    | Plus, _ -> App (exp1, step1 exp2) (* Arith_plus *)
    | Minus, Pair (Num(i1), Num(i2)) -> Num(i1-i2) (* Minus *)
    | Minus, _ -> App (exp1, step1 exp2) (* Arith_minus *)
    | Eq, Pair (Num(i1), Num(i2)) -> if i1 = i2 then True else False (* Eq, Eq' *)
    | Eq, _ -> App (exp1, step1 exp2) (* Arith_eq *)
    | Lam(exp), _ -> if isitvalue exp2 then subst exp exp2 0 (* App *) else App(exp1, step1 exp2) (* Arg *) 
    | _, _ -> App(exp1, step1 exp2) (* Arg *)
    end else App (step1 exp1, exp2) (* Lam *)
  | Pair (exp1, exp2) -> if isitvalue exp1 then Pair (exp1, step1 exp2) else Pair (step1 exp1, exp2) (* Pair, Pair' *)
  | Fst (exp) -> begin match exp with
    | Pair (e1, e2) -> if isitvalue e1 && isitvalue e2 then e1 else Fst (step1 exp) (* Fst' *)
    | _ -> Fst (step1 exp) (* Fst *)
    end
  | Snd (exp) -> begin match exp with
    | Pair (e1, e2) -> if isitvalue e1 && isitvalue e2 then e2 else Snd (step1 exp) (* Snd' *)
    | _ -> Snd (step1 exp) (* Snd *)
    end
  | Eunit -> raise Stuck
  | Inl (exp) -> Inl (step1 exp) (* Inl *)
  | Inr (exp) -> Inr (step1 exp) (* Inr *)
  | Case (exp1, exp2, exp3) -> begin match exp1 with
    | Inl var -> if isitvalue var then subst exp2 var 0 else Case((step1 exp1), exp2, exp3) (* Case' *)
    | Inr var -> if isitvalue var then subst exp3 var 0 else Case((step1 exp1), exp2, exp3) (* Case'' *)
    | _ -> Case(step1 exp1, exp2, exp3) (* Case *)
    end
  | Fix (exp) -> let sub = (subst exp (Fix (exp)) 0) in if Fix (exp) = sub then exp else sub (* Fix *)
  | True -> raise Stuck
  | False -> raise Stuck
  | Ifthenelse (tf, exp1, exp2) -> begin match tf with 
    | True -> exp1 (* If_true *)
    | False -> exp2 (* If_false *)
    | _ -> Ifthenelse (step1 tf, exp1, exp2) (* If *)
    end
  | Num (i) -> raise Stuck
  | Plus -> raise Stuck
  | Minus -> raise Stuck
  | Eq -> raise Stuck

(* Problem 3. 
 * step2 : state -> state *)
let step2 state =
  let exp2val exp' =
    match exp' with
    | Ind (index) -> Indv (index) 
    | Lam (exp) -> Lamv (exp) 
    | App (exp1, exp2) -> Appv (exp1, exp2)
    | Pair (exp1, exp2) -> Pairv (exp1, exp2)
    | Fst (exp) -> Fstv (exp) 
    | Snd (exp) -> Sndv (exp) 
    | Eunit -> Eunitv
    | Inl (exp) -> Inlv (exp) 
    | Inr (exp) -> Inrv (exp) 
    | Case (exp1, exp2, exp3) -> Casev (exp1, exp2, exp3)
    | True -> Truev
    | False -> Falsev
    | Ifthenelse (exp1, exp2, exp3) -> Ifthenelsev (exp1, exp2, exp3)
    | Num (int) -> Numv (int)
    | Plus -> Plusv
    | Minus -> Minusv
    | Eq -> Eqv
    | _ -> raise Stuck
  in
  match state with
    | Anal_ST (stov, stack, exp', env) -> 
      begin match exp' with
        | Lam (exp) -> begin try match Heap.deref stov (env exp) with 
          | Computed(value) -> Return_ST ((Heap.update stov (env exp) (Delayed (exp, env))), stack, exp2val exp')
          | Delayed(_, env') -> begin match (Heap.allocate stov (Delayed(exp, env'))) with
            | (newOval, num) -> Anal_ST (newOval, (Frame_SK (stack, Lam_Fr(Hole_Fr))), exp, (fun e -> match e with exp -> num | _ -> env e))
          end
          with Heap.InvalidLocation -> begin match (Heap.allocate stov (Delayed(exp', env))) with
            | (newOval, num) -> Anal_ST (newOval, (Frame_SK (stack, Lam_Fr(Hole_Fr))), exp, (fun e -> match e with exp -> num | _ -> env e))
          end
        end
        | App (exp1, exp2) ->
          begin match exp1, exp2 with
            | Plus, Pair (Num(i1), Num(i2)) -> Anal_ST (stov, stack, Num(i1+i2), env)
            | Minus, Pair (Num(i1), Num(i2)) -> Anal_ST (stov, stack, Num(i1-i2), env) 
            | Eq, Pair (Num(i1), Num(i2)) -> Anal_ST (stov, stack, (if i1 = i2 then True else False), env)
            | Lam(exp), _ -> begin try match Heap.deref stov (env exp2) with 
              | Computed(value) -> Anal_ST (Heap.update stov (env exp2) (Delayed (exp', env)), stack, (step1 exp'), env)
              | Delayed(_, env') -> Anal_ST (stov, (Frame_SK (stack,App'_Fr(exp1, Hole_Fr))), exp2, env')
              with Heap.InvalidLocation -> begin match (Heap.allocate stov (Delayed(exp2, env))) with
                | (newOval, num) -> Anal_ST (newOval, (Frame_SK (stack, App'_Fr(exp1, Hole_Fr))), exp2, (fun e -> match e with exp2 -> num | _ -> env e))
              end
            end
            | _, _ -> if env exp1 > 0 then begin match Heap.deref stov (env exp1) with 
              | Computed(value) -> if env exp2 > 0 then begin match Heap.deref stov (env exp2) with 
                | Computed(value) -> Return_ST ((Heap.update stov (env exp2) (Delayed (exp2, env))), stack, exp2val exp')
                | Delayed(_, env') -> begin match (Heap.allocate stov (Delayed(exp2, env'))) with
                  | (newOval, num) -> Anal_ST (newOval, (Frame_SK (stack, App'_Fr(exp1, Hole_Fr))), exp2, (fun e -> match e with exp2 -> num | _ -> env e))
                end
              end
                else begin match (Heap.allocate stov (Delayed(exp2, env))) with
                  | (newOval, num) -> Anal_ST (newOval, (Frame_SK (stack, App'_Fr(exp1, Hole_Fr))), exp2, (fun e -> match e with exp2 -> num | _ -> env e))
                end
              | Delayed(_, env') -> begin match (Heap.allocate stov (Delayed(exp1, env'))) with
                | (newOval, num) -> Anal_ST (newOval, (Frame_SK (stack, App_Fr(Hole_Fr, exp2))), exp1, (fun e -> match e with exp1 -> num | _ -> env e))
              end 
            end
              else begin match (Heap.allocate stov (Delayed(exp1, env))) with
                | (newOval, num) -> Anal_ST (newOval, (Frame_SK (stack, App_Fr(Hole_Fr, exp2))), exp1, (fun e -> match e with exp1 -> num | _ -> env e))
              end
          end
        | Pair (exp1, exp2) -> 
          if env exp1 > 0 then begin match Heap.deref stov (env exp1) with 
            | Computed(value) -> if env exp2 > 0 then begin match Heap.deref stov (env exp2) with 
              | Computed(value) -> Return_ST ((Heap.update stov (env exp2) (Delayed (exp2, env))), stack, exp2val exp')
              | Delayed(_, env') -> begin match (Heap.allocate stov (Delayed(exp2, env'))) with
                | (newOval, num) -> Anal_ST (newOval, (Frame_SK (stack, Pair'_Fr(exp1, Hole_Fr))), exp2, (fun e -> match e with exp2 -> num | _ -> env e))
              end
            end
              else begin match (Heap.allocate stov (Delayed(exp2, env))) with
                | (newOval, num) -> Anal_ST (newOval, (Frame_SK (stack, Pair'_Fr(exp1, Hole_Fr))), exp2, (fun e -> match e with exp2 -> num | _ -> env e))
              end
            | Delayed(_, env') -> begin match (Heap.allocate stov (Delayed(exp1, env'))) with
              | (newOval, num) -> Anal_ST (newOval, (Frame_SK (stack, Pair_Fr(Hole_Fr, exp2))), exp1, (fun e -> match e with exp1 -> num | _ -> env e))
            end 
          end
            else begin match (Heap.allocate stov (Delayed(exp1, env))) with
              | (newOval, num) -> Anal_ST (newOval, (Frame_SK (stack, Pair_Fr(Hole_Fr, exp2))), exp1, (fun e -> match e with exp1 -> num | _ -> env e))
            end
        | Fst (exp) -> begin match exp with 
          | Pair(exp1, exp2) -> Anal_ST (stov, stack, exp1, env)
          | _ -> begin try match Heap.deref stov (env exp) with 
            | Computed(value) -> Return_ST ((Heap.update stov (env exp) (Delayed (exp', env))), stack, exp2val exp')
            | Delayed(_, env') -> begin match (Heap.allocate stov (Delayed(exp, env'))) with
              | (newOval, num) -> Anal_ST (newOval, (Frame_SK (stack, Fst_Fr(Hole_Fr))), exp, (fun e -> match e with exp -> num | _ -> env e))
            end
            with Heap.InvalidLocation -> begin match (Heap.allocate stov (Delayed(exp, env))) with
              | (newOval, num) -> Anal_ST (newOval, (Frame_SK (stack, Fst_Fr(Hole_Fr))), exp, (fun e -> match e with exp -> num | _ -> env e))
            end
          end
        end
        | Snd (exp) -> begin match exp with 
          | Pair(exp1, exp2) -> Anal_ST (stov, stack, exp2, env)
          | _ -> begin try match Heap.deref stov (env exp) with 
            | Computed(value) -> Return_ST ((Heap.update stov (env exp) (Delayed (exp', env))), stack, exp2val exp')
            | Delayed(_, env') -> begin match (Heap.allocate stov (Delayed(exp, env'))) with
              | (newOval, num) -> Anal_ST (newOval, (Frame_SK (stack, Snd_Fr(Hole_Fr))), exp, (fun e -> match e with exp -> num | _ -> env e))
            end
            with Heap.InvalidLocation -> begin match (Heap.allocate stov (Delayed(exp, env))) with
              | (newOval, num) -> Anal_ST (newOval, (Frame_SK (stack, Snd_Fr(Hole_Fr))), exp, (fun e -> match e with exp -> num | _ -> env e))
            end
          end
        end
        | Inl (exp) -> begin try match Heap.deref stov (env exp) with 
          | Computed(value) -> Return_ST ((Heap.update stov (env exp) (Delayed (exp', env))), stack, exp2val exp')
          | Delayed(_, env') -> begin match (Heap.allocate stov (Delayed(exp, env'))) with
            | (newOval, num) -> Anal_ST (newOval, (Frame_SK (stack, Inl_Fr(Hole_Fr))), exp, (fun e -> match e with exp -> num | _ -> env e))
          end
          with Heap.InvalidLocation -> begin match (Heap.allocate stov (Delayed(exp, env))) with
            | (newOval, num) -> Anal_ST (newOval, (Frame_SK (stack, Inl_Fr(Hole_Fr))), exp, (fun e -> match e with exp -> num | _ -> env e))
          end
        end
        | Inr (exp) -> begin try match Heap.deref stov (env exp) with 
          | Computed(value) -> Return_ST ((Heap.update stov (env exp) (Delayed (exp', env))), stack, exp2val exp')
          | Delayed(_, env') -> begin match (Heap.allocate stov (Delayed(exp, env'))) with
            | (newOval, num) -> Anal_ST (newOval, (Frame_SK (stack, Inr_Fr(Hole_Fr))), exp, (fun e -> match e with exp -> num | _ -> env e))
          end
          with Heap.InvalidLocation -> begin match (Heap.allocate stov (Delayed(exp, env))) with
            | (newOval, num) -> Anal_ST (newOval, (Frame_SK (stack, Inr_Fr(Hole_Fr))), exp, (fun e -> match e with exp -> num | _ -> env e))
          end
        end
        | Case (exp1, exp2, exp3) -> begin match exp1 with
          | Inl (exp) -> Anal_ST (stov, stack, (step1 (App(Lam(exp2), exp))), env)
          | Inr (exp) -> Anal_ST (stov, stack, (step1 (App(Lam(exp3), exp))), env)
          | _ -> begin try match Heap.deref stov (env exp1) with 
            | Computed(value) -> Return_ST ((Heap.update stov (env exp1) (Delayed (exp', env))), stack, exp2val exp')
            | Delayed(_, env') -> Anal_ST (stov, (Frame_SK (stack, Case_Fr(Hole_Fr, exp2, exp3))), exp1, env')
            with Heap.InvalidLocation -> begin match (Heap.allocate stov (Delayed(exp', env))) with
              | (newOval, num) -> Anal_ST (newOval, (Frame_SK (stack, Case_Fr(Hole_Fr, exp2, exp3))), exp1, (fun e -> match e with exp1 -> num | _ -> env e))
            end
          end
        end
        | Fix (exp) -> begin match (Heap.allocate stov (Delayed(exp', env))) with 
          | (newOval, num) -> Anal_ST (newOval, stack, step1 exp', (fun e -> match e with exp' -> num | _ -> env e))
        end
        | Ifthenelse (tf, exp1, exp2) ->
          begin match tf with
            | True -> Anal_ST (stov, stack, exp1, env)
            | False -> Anal_ST (stov, stack, exp2, env)
            | _ -> begin try match Heap.deref stov (env tf) with 
              | Computed(value) -> Return_ST ((Heap.update stov (env tf) (Delayed (exp', env))), stack, exp2val exp')
              | Delayed(_, env') -> begin match (Heap.allocate stov (Delayed(tf, env'))) with
                | (newOval, num) -> Anal_ST (newOval, (Frame_SK (stack, Ifthenelse_Fr(Hole_Fr, exp1, exp2))), tf, (fun e -> match e with tf -> num | _ -> env e))
              end
              with Heap.InvalidLocation -> begin match (Heap.allocate stov (Delayed(tf, env))) with
                | (newOval, num) -> Anal_ST (newOval, (Frame_SK (stack, Ifthenelse_Fr(Hole_Fr, exp1, exp2))), tf, (fun e -> match e with tf -> num | _ -> env e))
              end
            end
          end
        | _ -> begin try match Heap.deref stov (env exp') with 
          | _ -> Return_ST ((Heap.update stov (env exp') (Delayed (exp', env))), stack, exp2val exp')
          with Heap.InvalidLocation -> begin match (Heap.allocate stov (Delayed(exp', env))) with
              | (newOval, num) -> Return_ST (Heap.update newOval num (Delayed(exp', (fun e -> match e with exp' -> num | _ -> env e))), stack, exp2val exp')
          end
        end
      end
    | Return_ST (stov,stack,value) -> 
      match stack with 
        | Hole_SK -> if step1(value2exp value) = (value2exp value) then raise Stuck else Anal_ST (Heap.empty, stack, (step1(value2exp value)), emptyEnv)
        | Frame_SK(stk, frame) ->
            let findHeap heap exp =
              let rec findHeap' heap exp num =
                try match (Heap.deref heap num) with Delayed(exp', _) -> if exp' = exp then num else findHeap' heap exp (num+1)
                                                | _ -> findHeap' heap exp (num+1)
                with Heap.InvalidLocation -> if num = 1 then 1 else num-1
              in
              findHeap' heap exp 1
            in
            let vexp = value2exp value in
            let num = (findHeap stov vexp) in
            match (Heap.deref stov num) with
              | Delayed(exp', env') ->
                let env' = fun e -> if e = exp' then num else env' e in
                let newStov = (Heap.update stov num (Computed (value))) in
                begin match frame with
                | Lam_Fr (Hole_Fr) -> Anal_ST (newStov, stk, Lam(value2exp value), env')
                | App_Fr (Hole_Fr, exp) -> Anal_ST (newStov, stk, App(value2exp value, exp), env')
                | App'_Fr (exp, Hole_Fr) -> Anal_ST (newStov, stk, App(exp, value2exp value), env')
                | Pair_Fr (Hole_Fr, exp) -> Anal_ST (newStov, stk, Pair(value2exp value, exp), env')
                | Pair'_Fr (exp, Hole_Fr) -> Anal_ST (newStov, stk, Pair(exp, value2exp value), env')
                | Fst_Fr (Hole_Fr) -> Anal_ST (newStov, stk, Fst(value2exp value), env')
                | Snd_Fr (Hole_Fr) -> Anal_ST (newStov, stk, Snd(value2exp value), env')
                | Inl_Fr (Hole_Fr) -> Anal_ST (newStov, stk, Inl(value2exp value), env')
                | Inr_Fr (Hole_Fr) -> Anal_ST (newStov, stk, Inr(value2exp value), env')
                | Case_Fr (Hole_Fr, exp1, exp2) -> Anal_ST (newStov, stk, Case(value2exp value, exp1, exp2), env')
                | Ifthenelse_Fr (Hole_Fr, exp1, exp2) -> Anal_ST (newStov, stk, Ifthenelse(value2exp value, exp1, exp2), env')
                | Fix_Fr (Hole_Fr) -> Anal_ST (newStov, stk, step1(Fix(value2exp value)), env')
                | _ -> raise Stuck
                end
              | Computed (_) -> raise Stuck
                        
(* exp2string : Tml.exp -> string *)
let rec exp2string exp = 
  match exp with 
    Ind x -> string_of_int x
  | Lam e -> "(lam. " ^ (exp2string e) ^ ")"
  | App (e1, e2) -> "(" ^ (exp2string e1) ^ " " ^ (exp2string e2) ^ ")"
  | Pair (e1, e2) -> "(" ^ (exp2string e1) ^ "," ^ (exp2string e2) ^ ")"
  | Fst e -> "(fst " ^ (exp2string e) ^ ")"
  | Snd e -> "(snd " ^ (exp2string e) ^ ")"
  | Eunit -> "()"
  | Inl e -> "(inl " ^ (exp2string e) ^ ")"
  | Inr e -> "(inr " ^ (exp2string e) ^ ")"
  | Case (e, e1, e2) -> "(case " ^ (exp2string e) ^" of " ^ (exp2string e1) ^
                          " | " ^ (exp2string e2) ^ ")"
  | Fix e -> "(fix. "  ^ (exp2string e) ^ ")"
  | Ifthenelse (e, e1, e2) -> 
     "(if " ^ (exp2string e) ^ " then " ^ (exp2string e1) ^ 
       " else " ^ (exp2string e2) ^ ")"
  | True -> "true"  | False -> "false"
  | Num n -> "<" ^ (string_of_int n) ^ ">"
  | Plus -> "+"  | Minus -> "-" | Eq -> "="

(* state2string : state -> string 
 * you may modify this function for debugging your code *)
let state2string st =
  let rec stack2string stack = 
    let frame2string frame = 
      begin match frame with
        | Hole_Fr -> "[]" 
        | Value_Fr (value) -> exp2string(value2exp value) 
        | Lam_Fr (Hole_Fr) -> "(lam [])"
        | Exp_Fr (exp) -> exp2string exp
        | App_Fr (Hole_Fr, exp) -> "([] " ^ (exp2string exp) ^ ")"
        | App'_Fr (exp, Hole_Fr) -> "("^ (exp2string exp) ^ "[])"
        | Pair_Fr (Hole_Fr, exp) -> "([], " ^ (exp2string exp) ^ ")"
        | Pair'_Fr (exp, Hole_Fr) -> "("^ (exp2string exp) ^ ", [])"
        | Fst_Fr (Hole_Fr) -> "(fst [])"
        | Snd_Fr (Hole_Fr) -> "(snd [])"
        | Inl_Fr (Hole_Fr) -> "(inl [])"
        | Inr_Fr (Hole_Fr) -> "(inr [])"
        | Case_Fr (Hole_Fr, e1, e2) ->  "(case [] of " ^ (exp2string e1) ^ " | " ^ (exp2string e2) ^ ")"
        | Ifthenelse_Fr (Hole_Fr, e1, e2) ->  "(if [] then " ^ (exp2string e1) ^ " else " ^ (exp2string e2) ^ ")"
        | _ -> " !!!!! "
      end
    in
    begin match stack with
      | Hole_SK -> "[]"
      | Frame_SK (stack, frame) -> (stack2string stack) ^ " | " ^ (frame2string frame)
    end
  in
  match st with
    Anal_ST(_,stack,exp,env) -> "Analysis: " ^ (stack2string stack) ^ " || " ^ (exp2string exp) ^ " || E: " ^ (exp2string(Num (env exp)))
  | Return_ST(_,stack,value) -> "Return: " ^ (stack2string stack) ^ " || " ^ (exp2string (value2exp value))

(* ------------------------------------------------------------- *)     
let stepOpt1 e = try Some (step1 e) with Stuck -> None
let stepOpt2 st = try Some (step2 st) with Stuck -> None

let rec multiStep1 e = try multiStep1 (step1 e) with Stuck -> e
let rec multiStep2 st = try multiStep2 (step2 st) with Stuck -> st

let stepStream1 e =
  let rec steps e = 
    match (stepOpt1 e) with
      None -> Stream.from (fun _ -> None)
    | Some e' -> Stream.icons e' (steps e')
  in 
  Stream.icons e (steps e)

let stepStream2 st =
  let rec steps st = 
    match (stepOpt2 st) with
      None -> Stream.from (fun _ -> None)
    | Some st' -> Stream.icons st' (steps st')
  in 
  Stream.icons st (steps st)
