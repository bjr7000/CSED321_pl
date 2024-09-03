open Mach
open Mono 

exception NotImplemented
exception Here

(* location *)
type loc =
    L_INT of int          (* integer constant *)
  | L_BOOL of bool        (* boolean constant *)
  | L_UNIT                (* unit constant *)
  | L_STR of string       (* string constant *)
  | L_ADDR of Mach.addr   (* at the specified address *)
  | L_REG of Mach.reg     (* at the specified register *)
  | L_DREF of loc * int   (* at the specified location with the specified offset *)

type venv = (Mono.avid, loc) Dict.dict  (* variable environment *)
let venv0 : venv = Dict.empty           (* empty variable environment *)

type env = venv * int
let env0 : env = (venv0, 0)

(* val loc2rvalue : loc -> Mach.code * rvalue *)
let rec loc2rvalue l = match l with
    L_INT i -> (Mach.code0, Mach.INT i)
  | L_BOOL b -> (Mach.code0, Mach.BOOL b)
  | L_UNIT -> (Mach.code0, Mach.UNIT)
  | L_STR s -> (Mach.code0, Mach.STR s)
  | L_ADDR a -> (Mach.code0, Mach.ADDR a)
  | L_REG r -> (Mach.code0, Mach.REG r)
  | L_DREF (L_ADDR a, i) -> (Mach.code0, Mach.REFADDR (a, i))
  | L_DREF (L_REG r, i) -> (Mach.code0, Mach.REFREG (r, i))
  | L_DREF (l, i) ->
     let (code, rvalue) = loc2rvalue l in
     (Mach.cpost code [Mach.MOVE (Mach.LREG Mach.tr, rvalue)], Mach.REFREG (Mach.tr, i))

(*
 * helper functions for debugging
 *)
(* val loc2str : loc -> string *)
let rec loc2str l = match l with 
    L_INT i -> "INT " ^ (string_of_int i)
  | L_BOOL b -> "BOOL " ^ (string_of_bool b)
  | L_UNIT -> "UNIT"
  | L_STR s -> "STR " ^ s
  | L_ADDR (Mach.CADDR a) -> "ADDR " ^ ("&" ^ a)
  | L_ADDR (Mach.HADDR a) -> "ADDR " ^ ("&Heap_" ^ (string_of_int a))
  | L_ADDR (Mach.SADDR a) -> "ADDR " ^ ("&Stack_" ^ (string_of_int a))
  | L_REG r -> 
     if r = Mach.sp then "REG SP"
     else if r = Mach.bp then "REG BP"
     else if r = Mach.cp then "REG CP"
     else if r = Mach.ax then "REG AX"
     else if r = Mach.bx then "REG BX"
     else if r = Mach.tr then "REG TR"
     else if r = Mach.zr then "REG ZR"
     else "R[" ^ (string_of_int r) ^ "]"
  | L_DREF (l, i) -> "DREF(" ^ (loc2str l) ^ ", " ^ (string_of_int i) ^ ")"

(*
 * Generate code for Abstract Machine MACH 
 *)
(* pat2code : Mach.label -> Mach.label -> loc -> Mono.pat -> Mach.code * venv *)
(* patty2code : Mach.label -> Mach.label -> loc -> Mono.patty -> Mach.code * venv *)
let rec patty2code startadr failadr lc patty = 
  let pat2code startadr failadr' lc pattern = 
    let (code, rv) = loc2rvalue lc in
    let failadr = (ADDR (CADDR failadr')) in
    let codeenv =
      match pattern with
      | P_WILD -> (code0, venv0)
      | P_INT (i) -> ((clist [JMPNEQ (failadr, rv, INT i)]), venv0)
      | P_BOOL (b) -> ((clist [XOR(LREG(r10), rv, BOOL(b)); JMPTRUE(failadr, REG(r10))]), venv0)
      | P_UNIT -> let cd = if rv = UNIT then code0 else clist [JUMP(failadr)] in (cd, venv0)
      | P_VID (vid) -> begin match snd vid with
        | VAR -> ((clist [POP(LREG(r12)); RETURN]), Dict.singleton (fst vid, lc))
        | CON -> ((clist [JMPNEQSTR(failadr, STR(fst vid), rv)]), Dict.singleton (fst vid, lc))
        | CONF -> ((clist [POP(LREG(r12)); RETURN]), Dict.singleton (fst vid, lc))
        end
      | P_VIDP (vid, patty) -> let pt = patty2code startadr failadr' lc patty in (fst pt, Dict.singleton (fst vid, lc))
      | P_PAIR (patty1, patty2) -> let p1 = patty2code startadr failadr' lc patty1 in let p2 = patty2code startadr failadr' lc patty2 in
                                   ((fst p1)@@(fst p2), (Dict.merge (snd p1) (snd p2)))
    in
    (code @@ (fst codeenv), (snd codeenv))
  in
  match patty with
  | PATTY (P_WILD, _) -> pat2code startadr failadr lc P_WILD
  | PATTY (P_INT(i), T_INT) -> pat2code startadr failadr lc (P_INT(i))
  | PATTY (P_BOOL(b), T_BOOL) -> pat2code startadr failadr lc (P_BOOL(b))
  | PATTY (P_UNIT, T_UNIT) -> pat2code startadr failadr lc P_UNIT
  | PATTY (P_VID(vid), _) -> pat2code startadr failadr lc (P_VID(vid))
  | PATTY (P_VIDP(vid, ptyp), _) -> pat2code startadr failadr lc (P_VIDP(vid, ptyp))
  | PATTY (P_PAIR(ptyp1, ptyp2), T_PAIR(typ1, typ2)) -> pat2code startadr failadr lc (P_PAIR(ptyp1, ptyp2))
  | _ -> (code0, venv0)

(* expty2code : env -> Mach.label -> Mono.expty -> int -> Mach.code * Mach.rvalue *)
(* exp2code : env -> Mach.label -> Mono.exp -> int -> Mach.code * Mach.rvalue *)
let rec expty2code env lb expty n =  
  let exp2code env lb exp n = 
    match exp with
    | E_INT (i) -> (clist [PUSH(INT (i))], INT i)
    | E_BOOL (b) -> (clist [PUSH(BOOL (b))], BOOL b)
    | E_UNIT -> (clist [PUSH(STR("()"))], UNIT)
    | E_PLUS -> (clist [POP(LREG(r10)); PUSH(REFREG(r10, 0)); PUSH(REFREG(r10, 1)); FREE(REG(r10)); POP(LREG(r10)); POP(LREG(r11)); 
                        ADD(LREG(r10), REG(r10), REG(r11)); PUSH(REG(r10))], REFREG(r10,0))
    | E_MINUS -> (clist [POP(LREG(r10)); PUSH(REFREG(r10, 0)); PUSH(REFREG(r10, 1)); FREE(REG(r10)); POP(LREG(r10)); POP(LREG(r11)); 
                         SUB(LREG(r10), REG(r11), REG(r10)); PUSH(REG(r10))], REFREG(r10,0))
    | E_MULT -> (clist [POP(LREG(r10)); PUSH(REFREG(r10, 0)); PUSH(REFREG(r10, 1)); FREE(REG(r10)); POP(LREG(r10)); POP(LREG(r11)); 
                        MUL(LREG(r10), REG(r10), REG(r11)); PUSH(REG(r10))], REFREG(r10,0))
    | E_EQ -> (clist [POP(LREG(r10)); PUSH(REFREG(r10, 0)); PUSH(REFREG(r10, 1)); FREE(REG(r10)); POP(LREG(r10)); POP(LREG(r11)); 
                      JMPNEQ(ADDR(CADDR(lb^"_1")), REG(r10), REG(r11)); MOVE(LREG(r10), BOOL(true)); JUMP(ADDR(CADDR(lb^"_2")));
                      LABEL(lb^"_1"); MOVE(LREG(r10), BOOL(false)); LABEL(lb^"_2"); PUSH(REG(r10))], REFREG(r10,0)) 
    | E_NEQ ->  (clist [POP(LREG(r10)); PUSH(REFREG(r10, 0)); PUSH(REFREG(r10, 1)); FREE(REG(r10)); POP(LREG(r10)); POP(LREG(r11)); 
                        JMPNEQ(ADDR(CADDR(lb^"_1")), REG(r10), REG(r11)); MOVE(LREG(r10), BOOL(false)); JUMP(ADDR(CADDR(lb^"_2")));
                        LABEL(lb^"_1"); MOVE(LREG(r10), BOOL(true)); LABEL(lb^"_2"); PUSH(REG(r10))], REFREG(r10,0))
    | E_VID (vid) -> let rv = Dict.lookup (fst vid) (fst env) in 
                    begin match snd vid with
                    | VAR ->
                      let argRecover =
                        let rec argRecover' n ac =
                          if n = 0 then ([MOVE(LREFREG(fx, 1), REG(r13))],[MOVE(LREG(r13), REFREG(fx, 1))]) 
                          else argRecover' (n-1) ([MOVE(LREFREG(fx, n+1), REG(r13+n))]@(fst ac),[MOVE(LREG(r13+n), REFREG(fx, n+1))]@(snd ac))
                        in
                        argRecover' n ([],[])
                      in
                      begin match rv with 
                        | None -> (code0, UNIT)
                        | Some L_DREF (L_ADDR a, 0) -> 
                          let lb = labelNew () in
                        ((clist [ADD(LREG(cx), REG(cx), INT(1)); MOVE(LREG(bx), REG(dx)); MALLOC(LREG(dx), INT(2)); MOVE(LREFREG(dx, 1), REG(bx)); 
                                  MALLOC(LREG(bx), INT(n+2)); MOVE(LREFREG(bx, 0), REG(fx)); MOVE(LREG(fx), REG(bx))])@@(fst argRecover)@@
                          (clist [CALL(ADDR(a)); LABEL(lb^"_ret"); JMPNEQ(ADDR(CADDR(lb^"_StackClean")), REFREG(dx, 0), INT(0)); JUMP(ADDR(CADDR(lb^"_StackDone"))); 
                                  LABEL(lb^"_StackClean"); POP(LREG(r13)); SUB(LREFREG(dx, 0), REFREG(dx, 0), REG(cx)); JUMP(ADDR(CADDR(lb^"_ret")));
                                  LABEL(lb^"_StackDone")])@@(snd argRecover)@@
                          (clist [MOVE(LREG(bx), REG(fx)); MOVE(LREG(fx), REFREG(fx, 0)); FREE(REG(bx)); MOVE(LREG(bx), REG(dx));
                                  MOVE(LREG(dx), REFREG(dx, 1)); FREE(REG(bx)); SUB(LREG(cx), REG(cx), INT(1)); PUSH(REG(r12))]), UNIT)
                        | Some v -> let l2r = (loc2rvalue v) in ((fst l2r)@@(clist [PUSH (snd l2r)]), (snd l2r))
                      end
                    | CON -> begin match rv with 
                      | None -> ((clist [MALLOC(LREG(gx), INT(1)); MOVE(LREFREG(gx, 0), STR(fst vid)); PUSH(REG(gx))]), STR(fst vid)) 
                      | Some v -> let l2r = (loc2rvalue v) in ((fst l2r)@@(clist [PUSH (snd l2r)]), (snd l2r))
                      end
                    | CONF -> (clist [MALLOC(LREG(gx),INT(2)); POP(LREFREG(gx,1)); MOVE(LREFREG(gx,0), STR(fst vid)); PUSH(REG(gx))], STR(fst vid))
                    end
    | E_FUN (rlist) -> let matching rlist =
                          let rec matching' rlist code =
                            match rlist with
                            | [] -> code
                            | M_RULE(p,e)::tl -> 
                              let ncode = (fst (expty2code env (labelNewStr (lb^"_Fn")) e (n+1)))@@(clist [JUMP(ADDR(CADDR(lb^"_FnEnd")))]) in
                              let nlb = labelNewStr (lb^"_Fn_") in
                              begin match p with
                                | PATTY (P_WILD, _) -> code@@ncode
                                | PATTY (P_INT(i), T_INT) -> matching' tl (code@@(clist [JMPNEQ(ADDR(CADDR(nlb)), REG(r13+n), INT(i))])@@ncode@@(clist [LABEL(nlb)]))
                                | PATTY (P_BOOL(b), T_BOOL) -> 
                                  matching' tl (code@@(clist [XOR(LREG(r13+n),REG(r13+n),BOOL(b));JMPTRUE(ADDR(CADDR(nlb)), REG(r13+n))])@@ncode@@(clist [LABEL(nlb)]))
                                | PATTY (P_UNIT, T_UNIT) -> matching' tl (code@@(clist [JMPNEQSTR(ADDR(CADDR(nlb)), REG(r13+n), STR("()"))])@@ncode@@(clist [LABEL(nlb)]))
                                | PATTY (P_VID(v), _) -> let nenv = ((Dict.insert ((fst v), L_REG(r13+n)) (fst env)), (snd env)+1) in
                                  begin match snd v with
                                    | VAR -> matching' tl (code@@(fst (expty2code nenv (labelNewStr (lb^"_Fn")) e (n+1)))@@(clist [JUMP(ADDR(CADDR(lb^"_FnEnd")))]))
                                    | CON -> matching' tl (code@@(clist [JMPNEQSTR(ADDR(CADDR(nlb)), REFREG(r13+n, 0), STR(fst v))])@@ncode@@(clist [LABEL(nlb)]))
                                    | CONF -> matching' tl (code@@(clist [JMPNEQSTR(ADDR(CADDR(nlb)), REFREG(r13+n, 0), STR(fst v))])@@ncode@@(clist [LABEL(nlb)]))
                                  end
                                | PATTY (P_VIDP(vid, ptyp), _) -> 
                                  let pt = matching' [M_RULE(ptyp, e)] code0 in
                                  matching' tl (code@@(clist [JMPNEQSTR(ADDR(CADDR(nlb)), REFREG(r13+n, 0), STR(fst vid)); MOVE(LREG(r28), REG(r13+n));
                                                              MOVE(LREG(r13+n), REFREG(r13+n, 1)); FREE(REG(r28)); MOVE(LREFREG(bp, (-3-n)), REG(r13+n))])
                                                    @@pt@@(clist [MOVE(LREFREG(bp, (-3-n)), REG(r13+n)); LABEL(nlb)]))
                                | PATTY (P_PAIR(ptyp1, ptyp2), T_PAIR(_, _)) -> 
                                  let rec pairMatch p psq env =
                                    match p with
                                    | PATTY (P_INT(i), T_INT) -> ((clist [JMPNEQ(ADDR(CADDR(nlb)), REFREG(r13+n, (psq mod 2)), INT(i))]), env)
                                    | PATTY (P_BOOL(b), T_BOOL) -> ((clist [XOR(LREG(r13+n), REFREG(r13+n, (psq mod 2)) ,BOOL(b)); JMPTRUE(ADDR(CADDR(nlb)), REG(r13+n))]), env)
                                    | PATTY (P_UNIT, T_UNIT) -> ((clist [JMPNEQSTR(ADDR(CADDR(nlb)), REFREG(r13+n, (psq mod 2)), STR("()"))]), env)
                                    | PATTY (P_VID(v), _) -> 
                                      let refs = 
                                        let rec refs' p = match p with
                                          | 2 -> (L_DREF(L_REG(r13+n), 0))
                                          | 3 -> (L_DREF(L_REG(r13+n), 1))
                                          | p -> (L_DREF((refs' (p/2)), (p mod 2)))
                                        in
                                        refs' (psq+2)
                                      in
                                      let nenv = ((Dict.insert ((fst v), refs) (fst env)), (snd env)+1) in (code0, nenv)
                                    | PATTY (P_VIDP(vid, ptyp), _) -> (code0, env)
                                    | PATTY (P_PAIR(p1, p2), T_PAIR(_, _)) -> 
                                      let p1 = pairMatch p1 (2*psq+2) env in let p2 = pairMatch p2 (2*psq+3) (snd p1) in
                                      (((clist [MALLOC(LREG(gx), INT(2));  MOVE(LREFREG(gx, 1), REG(r13+n)); MOVE(LREFREG(gx, 0), REG(r29));
                                                MOVE(LREG(r29), REG(gx)); MOVE(LREG(r13+n), REFREG(r13+n, (psq mod 2)));])@@(fst p1)@@(fst p2)@@
                                        (clist [MOVE(LREG(r13+n), REFREG(r29,1)); MOVE(LREG(gx), REFREG(r29, 0)); FREE(REG(r29)); MOVE(LREG(r29), REG(gx))])), (snd p2))
                                    | PATTY (P_WILD, _) -> (code0, env)
                                    | _ -> ((clist [JUMP(ADDR(CADDR(nlb)))]), env)
                                  in 
                                  let p1 = pairMatch ptyp1 0 env in
                                  let p2 = pairMatch ptyp2 1 (snd p1) in
                                  let ncode = (fst (expty2code (snd p2) (labelNewStr (lb^"_Fn")) e n))@@(clist [JUMP(ADDR(CADDR(lb^"_FnEnd")))]) in
                                  matching' tl (code@@(fst p1)@@(fst p2)@@ncode@@(clist [LABEL(nlb)]))
                                | _ -> matching' tl code
                              end
                          in
                          matching' rlist (clist [LABEL(lb^"_FnStart")])
                       in
                       ((clist [JMPNEQ(ADDR(CADDR(lb^"_callRead")),REG(cx),INT(0)); POP(LREG(r13+n)); JUMP(ADDR(CADDR(lb^"_FnStart"))); LABEL(lb^"_callRead"); 
                                MOVE(LREG(r13+n), REFREG(bp, (-3-n))); ADD(LREFREG(dx, 0), REFREG(dx, 0), REG(cx))])@@
                        (matching rlist)@@(clist [LABEL(lb^"_FnEnd")]), REFREG(r10,0))
    | E_APP (expty1, expty2) -> ((fst(expty2code env (labelNew ()) expty2 n))@@(fst(expty2code env (labelNew ()) expty1 n)), ADDR(CADDR(lb)))
    | E_PAIR (expty1, expty2) -> 
      let pairAlloc = 
        let rec code e handle=
          match e with
          | EXPTY (E_INT(i), T_INT) -> clist [MOVE(handle, INT(i))]
          | EXPTY (E_BOOL(b), T_BOOL) -> clist [MOVE(handle, BOOL(b))]
          | EXPTY (E_UNIT, T_UNIT) -> clist [MOVE(handle, STR("()"))]
          | EXPTY (E_VID(vid), _) -> (fst (expty2code env lb e n))@@(clist [POP(handle)])
          | EXPTY(E_PAIR(e1, e2), _) -> 
            let rhandle = match handle with LREFREG(r,i) -> REFREG(r,i) | LREFADDR(a,i) -> REFADDR(a,i) | LREG(r) -> REG(r) in
            clist [MALLOC(handle, INT(2)); MOVE(LREG(ex), rhandle)]@@(fst(expty2code env lb e1 n))@@(clist [POP(LREFREG(ex, 0))])
            @@(fst(expty2code env lb e2 n))@@(clist [POP(LREFREG(ex, 1)); MOVE(handle, REG(ex))])
          | EXPTY(E_APP(_, _), _) -> (fst (expty2code env lb e n))@@(clist [POP(handle)])
          | _ -> fst(expty2code env lb e n)
        in
        (code expty1 (LREFREG(ax, 0)))@@(code expty2 (LREFREG(ax, 1)))
      in
      ((clist [MOVE(LREG(gx),REG(ax)); MALLOC(LREG(ax), INT(2)); MOVE(LREFREG(ax, 1), REG(r29)); MOVE(LREFREG(ax, 0), REG(gx)); MOVE(LREG(r29), REG(ax));
               MALLOC(LREG(ax),INT(2))])@@pairAlloc@@
       (clist [PUSH(REG(ax)); MOVE(LREG(ax), REFREG(r29, 0)); MOVE(LREG(gx), REFREG(r29, 1)); FREE(REG(r29)); MOVE(LREG(r29), REG(gx))]), ADDR(CADDR(lb))) 
    | E_LET (dec, expty) -> let decs = dec2code (code0, env) (lb) dec in let exps = expty2code (snd decs) (lb) expty n in
                            ((fst decs)@@(fst exps), (snd exps))
  in
  match expty with
  | EXPTY (E_INT(i), T_INT) -> exp2code env lb (E_INT(i)) n
  | EXPTY (E_BOOL(b), T_BOOL) -> exp2code env lb (E_BOOL(b)) n
  | EXPTY (E_UNIT, T_UNIT) -> exp2code env lb E_UNIT n
  | EXPTY (E_PLUS, T_FUN (T_PAIR(T_INT,T_INT), T_INT)) -> exp2code env lb E_PLUS n
  | EXPTY (E_MINUS, T_FUN (T_PAIR(T_INT,T_INT), T_INT)) -> exp2code env lb E_MINUS n
  | EXPTY (E_MULT, T_FUN (T_PAIR(T_INT,T_INT), T_INT)) -> exp2code env lb E_MULT n
  | EXPTY (E_EQ, T_FUN (T_PAIR(T_INT,T_INT), T_BOOL)) -> exp2code env lb E_EQ n
  | EXPTY (E_NEQ, T_FUN (T_PAIR(T_INT,T_INT), T_BOOL)) -> exp2code env lb E_NEQ n
  | EXPTY (E_VID(vid), _) -> exp2code env lb (E_VID(vid)) n
  | EXPTY (E_FUN(rlist), T_FUN(_,_)) -> exp2code env lb (E_FUN(rlist)) n
  | EXPTY (E_APP(e1, e2), _) -> exp2code env lb (E_APP(e1, e2)) n
  | EXPTY (E_PAIR(e1, e2), T_PAIR(_,_)) -> exp2code env lb (E_PAIR(e1,e2)) n
  | EXPTY (E_LET(d, e), _) -> exp2code env lb (E_LET(d, e)) n
  | _ -> (code0, UNIT)
(* dec2code : Mach.code * env -> Mach.label -> Mono.dec -> Mach.code * env *)
and dec2code (code, env) lb dec =
  let envdict = fst env in
  let num = snd env in
  let loc = 
    let dec2loc dec =
      match dec with
      | D_VAL (PATTY(p, ptyp), EXPTY(e, etyp)) ->
        begin match e with
        | E_INT (i) -> L_INT(i)
        | E_BOOL (b) -> L_BOOL (b)
        | E_UNIT -> L_UNIT
        | E_VID(vid) -> begin match Dict.lookup (fst vid) envdict with None -> L_STR(fst vid) | Some l -> l end
        | _ -> L_DREF(L_ADDR(CADDR(lb)), 0)
        end
      | D_REC (PATTY(p, ptyp), EXPTY(e, etyp)) -> L_DREF(L_ADDR(CADDR(lb)), 0)
      | D_DTYPE -> L_INT(num)
    in
    match (Dict.lookup lb envdict) with None -> (dec2loc dec) | Some l -> l 
  in
  let nextlb = lb^"_fail" in
  let dec_anal = match dec with
    | D_VAL (patty, expty) -> ((patty2code lb nextlb loc patty), (expty2code env lb expty 0))
    | D_REC (patty, expty) -> let pt = (patty2code lb nextlb loc patty) in 
                              let key = begin match patty with 
                                | PATTY (P_VID(vid), _) -> [((fst vid), loc)]
                                | _ -> venv0 
                              end in
                              ((fst pt, (Dict.merge (snd pt) key)), (expty2code ((Dict.merge (snd pt) key), num+1) lb expty 0))
    | D_DTYPE -> ((code0, (Dict.singleton (lb, loc))), (code0, UNIT))
  in
  let addcode = (clist [LABEL(lb)]) @@ (fst(snd(dec_anal))) @@ (fst(fst(dec_anal))) @@ (clist [LABEL(nextlb);]) in
  let addenv = snd(fst(dec_anal)) in
  (code @@ addcode, ((Dict.merge envdict addenv), (num+1)))

(* program2code : Mono.program -> Mach.code *)
let program2code (dlist, et) = 
  let declaration =
    let rec declaration' dlist env =
      match dlist with
      | [] -> env
      | hd::tl -> declaration' tl (dec2code env (labelNew ()) hd)
    in
    declaration' dlist (code0, env0)
  in
  (clist [LABEL(Mach.start_label)]) @@ (fst (expty2code (snd declaration) (labelNew ()) et 0)) 
  @@ (clist [POP(LREG(ax)); HALT (REG(ax))]) @@ (fst declaration)
  