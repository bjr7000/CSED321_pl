open Fjava

exception NotImplemented
exception TypeError
exception Stuck
exception NotFound

let freshVarCounter = ref 0
let getFreshVariable s = 
  let _ = freshVarCounter := !freshVarCounter + 1 in
  s ^ (string_of_int (!freshVarCounter))
let data = ref []

let typeOf prog = 
  let classdic =
    let rec classdic' cls dic =
      match cls with
      | [] -> dic
      | (name, super, fields, constructor, methods)::tl 
          -> classdic' tl (fun n -> if n = name then ((super, fields), (constructor, methods)) else dic n)
    in
    classdic' (fst prog) (fun x -> raise TypeError)
  in
  let superdic clsName =
    let rec superdic' clsName lst =
      match clsName with
      | "Object" -> lst@(clsName::[])
      | _ -> superdic' (fst(fst(classdic clsName))) (lst@(clsName::[]))
    in
    superdic' clsName []
  in
  let fieldsdic cls fld =
    let rec fieldsdic' fieldList fld =
      begin match fieldList with
      | [] -> raise NotFound
      | (typ, name)::tl -> if name = fld then typ else fieldsdic' tl fld
      end 
    in
    fieldsdic' (snd(fst(classdic cls))) fld
  in
  let methodsdic cls mtd par =
    let rec parMatch par1 par2 =
      let rec typeMatch typ1 typ2 =
        match typ2 with
        | [] -> false
        | hd::tl -> if typ1 = hd then true else typeMatch typ1 tl
      in
      begin match par1, par2 with
      | [], [] -> true
      | [], hd::tl -> false
      | hd::tl, [] -> false 
      | (typ1, name1)::tl1, (typ2)::tl2 -> if typeMatch typ1 (superdic typ2) then parMatch tl1 tl2 else false
      end
    in
    let rec methodsdic' mtdList mtdName par =
      begin match mtdList with
      | [] -> raise NotFound
      | (ret, name, parList, body)::tl -> if (name = mtdName) && (parMatch parList par) then ret else methodsdic' tl mtdName par 
      end
    in
    methodsdic' (snd(snd(classdic cls))) mtd par
  in
  let rec expChecker exp =
    match exp with
      | Var (name) -> 
        let datacopy = !data in
        let rec dataminer n data=
          match data with
          | [] -> n
          | (v, f)::tl -> if n = v then expChecker(f (-1)) else dataminer n tl
        in
        dataminer name datacopy
      | Field (exp, name) -> 
        let rec fieldSuperCheck clsList name =
          begin match clsList with
          | [] -> raise TypeError
          | hd::tl -> try fieldsdic hd name with NotFound -> fieldSuperCheck tl name
          end 
        in
        fieldSuperCheck (superdic (expChecker exp)) name
      | Method (exp, name, expList) ->
        let rec methodSuperCheck clsList name par =
          begin match clsList with
          | [] -> raise TypeError
          | hd::tl -> try methodsdic hd name par with NotFound -> methodSuperCheck tl name par
          end 
        in
        let rec exp2par exps pars =
          begin match exps with
          | [] -> pars
          | hd::tl -> exp2par tl ((expChecker hd)::pars)
          end
        in
        methodSuperCheck (superdic (expChecker exp)) name (exp2par expList [])
      | New (typ, exps) -> let constructor = (fst(snd(classdic typ))) in
        let rec newchecker p e =
          let rec supernewchecker e' p' =
            begin match p' with
            | [] -> false
            | hd::tl -> if hd = e' then true else supernewchecker e' tl
            end
          in
          begin match p, e with
            | [], [] -> true
            | [], hd::tl -> false
            | hd::tl, [] -> false
            | (phd,_)::ptl, ehd::etl -> if supernewchecker phd (superdic (expChecker ehd)) then newchecker ptl etl else false
          end
        in
        begin match constructor with
          | (name, parList, superArg, assignments) -> if newchecker parList exps then name else raise TypeError
        end
      | Cast (changeTo, exp) -> let changeFrom = expChecker exp in
        let stupid e = print_endline "Stupid Warning"; e in
        let casting korewo koreni =
          let rec casting' korewo korenidic =
            begin match korenidic with
            | [] -> false
            | hd::tl -> if korewo = hd then true else casting' korewo tl
            end
          in
          casting' korewo (superdic koreni)
        in
        if casting changeTo changeFrom then changeTo (*upcast*)
        else if casting changeFrom changeTo then changeTo (*downcast*)
        else stupid changeTo (*stupidcast*)
  in
  expChecker (snd prog)
 
let step prog = 
  let classdic =
    let rec classdic' cls dic =
      match cls with
      | [] -> dic
      | (name, super, fields, constructor, methods)::tl 
          -> classdic' tl (fun n -> if n = name then ((super, fields), (constructor, methods)) else dic n)
    in
    classdic' (fst prog) (fun x -> raise Stuck)
  in
  let superdic clsName =
    let rec superdic' clsName lst =
      match clsName with
      | "Object" -> lst@(clsName::[])
      | _ -> superdic' (fst(fst(classdic clsName))) (lst@(clsName::[]))
    in
    superdic' clsName []
  in
  let redux = 
    let rec redux' exp =
      let datacopy = !data in
      match exp with
        | Var (name) -> exp
        | Field (callfrom, name) -> 
          begin match callfrom with
            | Var(cfrom) -> 
              let rec mining d v =
                match d with
                | [] -> raise Stuck
                | (var, f)::tl -> if v = var then f else mining tl v
              in
              let index n flist =
                let rec index' n flist num =
                  match flist with
                  | [] -> raise Stuck
                  | (_,hd)::tl -> if hd = n then num else index' n tl (num+1)
                in
                index' n flist 0
              in
              let constr = (fst(snd(classdic(typeOf(fst prog, callfrom))))) in
              begin match constr with (_,fl,_,_) -> (mining datacopy cfrom) (index name fl) end
            | _ -> Field((redux' callfrom), name)
          end
        | Method (callfrom, name, arglist) -> 
          begin match callfrom with
            | Var(cfrom) ->
              let callertype = typeOf(fst prog, callfrom) in
              let mtd =
                let methodmatching =
                  let rec methodmatching' classlist mname marg =
                    let rec argmatch a1 a2 =
                      let rec supermatch arg tplist =
                        begin match tplist with
                        | [] -> false
                        | hd::tl -> if hd = arg then true else supermatch arg tl
                        end
                      in
                      begin match a1, a2 with
                      | [], [] -> true
                      | [], hd::tl -> false
                      | hd::tl, [] -> false
                      | (h1, _)::t1, h2::t2 -> if supermatch h1 (superdic (typeOf (fst prog, h2))) then argmatch t1 t2 else false
                      end
                    in
                    begin match classlist with
                      | [] -> raise NotFound
                      | hd::tl ->
                        let rec methodmatching'' given mname marg =
                          begin match given with
                          | [] -> raise NotFound
                          | (retTyp, name, arglist, body)::tl ->
                            if name = mname && (argmatch arglist marg) then (retTyp, name, arglist, body)
                            else methodmatching'' tl mname marg
                          end
                        in
                        begin try (methodmatching'' (snd(snd(classdic hd))) mname marg) with NotFound -> methodmatching' tl mname marg end
                    end
                  in
                  methodmatching' (superdic callertype) name arglist
                in
                begin try methodmatching with NotFound -> raise Stuck end
              in
              let rec reducematch exp matchlist changelist =
                let rec reduce exp' tohere tothis =
                  let reducedlist list =
                    let rec reducedlist' list ret =
                      match list with
                        | [] -> ret
                        | hd::tl -> reducedlist' tl (ret@[(reduce hd tohere tothis)])
                    in
                    reducedlist' list []
                  in
                  begin match exp' with
                    | Var (name) -> if name = tohere then tothis else exp'
                    | Field (exp, str) -> Field((reduce exp tohere tothis), str)
                    | Method (exp, str, list) -> Method((reduce exp tohere tothis), str, (reducedlist list))
                    | New (typ, list) -> New (typ, (reducedlist list))
                    | Cast (typ, exp) -> Cast(typ, (reduce exp tohere tothis))
                  end
                in
                begin match matchlist, changelist with
                | [], [] -> exp
                | [], hd::tl -> raise Stuck
                | hd::tl, [] -> raise Stuck
                | mhd::mtl, chd::ctl -> reducematch (reduce exp mhd chd) mtl ctl
                end
              in
              let toherearg = 
                let rec toherearg' ret toherelist =
                  match toherelist with
                    | [] -> ret
                    | (_,str)::tl -> toherearg' (ret@[str]) tl
                in
                begin match mtd with
                  | (_,_,list,_) -> toherearg' [] list
                end
              in
              begin match mtd with
               | (_, name, _, body)-> reducematch body (["this"]@toherearg) ([callfrom]@arglist)
              end
            | _ -> Method((redux' callfrom), name, arglist)
          end
        | New (typ, constrArgs) ->
          let rec news typ args fieldfun num =
            match args with
            | [] -> let variable = (getFreshVariable typ) in
                    data := (variable, fieldfun)::!data;
                    Var(variable)
            | hd::tl -> news typ tl (fun index -> if index = num then hd else fieldfun index) (num+1)
          in
          let constrCorrect = try typeOf (fst prog, exp) with TypeError -> raise Stuck in
          news typ constrArgs (fun index -> if index = -1 then Var(typ) else raise Stuck) 0
        | Cast (towhat, fromwhat) -> let exptype = typeOf (fst prog, fromwhat) in
          let rec casting sprlist types =
            match sprlist with
            | [] -> false
            | hd::tl -> if types = hd then true else casting tl types
          in
          let wellcasted towhat fromwhat =
            let rec wellcastedf towhatfield fromwhatfield =
              begin match towhatfield, fromwhatfield with
              | [], _ -> true
              | hd::tl, [] -> false
              | (thd, tstr)::ttl, (fhd, fstr)::ftl -> if thd = fhd && tstr = fstr then wellcastedf ttl ftl else false
              end
            in
            let rec wellcastedm towhatmethod fromwhatmethod =
              let rec parMatch topar frompar =
                begin match topar, frompar with
                | [], [] -> true
                | [], hd::tl -> false
                | hd::tl, [] -> false
                | (thd, _)::ttl, (fhd, _)::ftl -> if thd = fhd then parMatch ttl ftl else false
                end
              in
              begin match towhatmethod, fromwhatmethod with
                | [], _ -> true
                | hd::tl, [] -> false
                | (totype, toname, topar, _)::ttl, (fromtype, fromname, frompar, _)::ftl -> 
                  if totype = fromtype && (parMatch topar frompar) && toname = fromname then wellcastedm ttl ftl else false
              end
            in
            (wellcastedf (snd(fst(classdic towhat))) (snd(fst(classdic fromwhat)))) && (wellcastedm (snd(snd(classdic towhat))) (snd(snd(classdic fromwhat))))
          in
          let datachangeforswap towhat name =
            let newname = (getFreshVariable towhat) in
            let rec datachangeforswap' oldname willread alreadyread =
              match willread with
                | [] -> raise Stuck
                | (hd, f)::tl -> 
                  if hd = oldname then data := alreadyread@[(newname, (fun i -> if i = (-1) then Var(towhat) else f i))]@willread 
                  else datachangeforswap' oldname tl (alreadyread@[(hd,f)])
            in
            if (datachangeforswap' name !data []) = () then Var(newname) else raise Stuck
          in
          if casting (superdic exptype) towhat then fromwhat
          else begin match fromwhat with 
            | Var(name) -> if casting (superdic towhat) exptype then 
                            if wellcasted towhat exptype then datachangeforswap towhat name
                            else raise Stuck 
                           else raise Stuck
            | _ -> Cast(towhat, (redux' fromwhat))
            end
    in
    redux' (snd prog)
  in
  if redux = (snd prog) then raise Stuck else (fst prog, redux)

let typeOpt p = try Some (typeOf p) with TypeError -> None
let stepOpt p = try Some (step p) with Stuck -> None
let rec multiStep p = try multiStep (step p) with Stuck -> p

let rec stepStream e =
  let rec steps e =
    match stepOpt e with
        None -> Stream.from (fun _ -> None)
      | Some e' -> Stream.icons e' (steps e')
  in Stream.icons e (steps e)
