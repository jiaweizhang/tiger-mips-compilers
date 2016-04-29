structure Semant =
struct

structure A = Absyn
structure E = Env
structure S = Symbol
structure T = Translate

type expty = {exp: T.exp, ty: Types.ty}
type venv = Env.enventry Symbol.table
type tenv = Types.ty Symbol.table

val DEBUG = false
val FOR_ESCAPE = false

val depth : int ref = ref 0
fun addDepth () = depth := !depth + 1
fun subDepth () = depth := !depth - 1
fun setDepth (newDepth) = depth := newDepth
fun getDepth () = !depth

fun typesEqual (a, b) = Types.check(a, b) = Types.SAM
fun typesNotEqual (a, b) = Types.check(a, b) <> Types.SAM
fun typesAssign (var, exp) = Types.check(var, exp) = Types.SAM orelse Types.check(var, exp) = Types.SUP
fun typesNotAssign (var, exp) = Types.check(var, exp) <> Types.SAM andalso Types.check(var, exp) <> Types.SUP

fun env_entry_toString(Env.VarEntry{access=access, ty=ty, assignable=assignable}) = Types.toString(ty)
  | env_entry_toString(Env.FunEntry{level, label, formals,result}) = "("^(String.concatWith "*" (map (Types.toString) formals))^"=>"^(Types.toString result)^")"

fun find_name(i:int) =
    let
          val tuples = (HashTable.listItemsi (Symbol.hashtable))
          fun find_helper(i:int,a::l : (string*int) list):string = if (#2 a) = i then (#1 a) else find_helper(i,l)
            | find_helper(i,[]) = "what"
    in 
        find_helper(i,tuples)
    end

fun print_tenv(some_env) = (print "TENV:";map (fn(tup)=>(print (#1 tup); print "->"; print (#2 tup); print " | ")) (map (fn(tup)=>(find_name (#1 tup),Types.toString(#2 tup)))(   Map.listItemsi(some_env))); print "\n")
fun print_venv(some_env) = (print "VENV:";map (fn(tup)=>(print (#1 tup); print "->"; print (#2 tup); print " | ")) (map (fn(tup)=>(find_name (#1 tup),env_entry_toString(#2 tup)))(   Map.listItemsi(some_env))); print "\n")

fun checkInt({exp,ty},pos) = case ty of 
                                    Types.INT => ()
                                  | _ => ErrorMsg.error pos " integer required"

fun checkIntOrString ({exp=_, ty=Types.INT}, {exp=_, ty=Types.INT}, pos) = ()
  | checkIntOrString ({exp=_, ty=Types.STRING}, {exp=_, ty=Types.STRING}, pos) = ()
  | checkIntOrString ({exp=_, ty=_ }, {exp=_, ty=_ }, pos) = ErrorMsg.error pos " integer or string required"

fun actual_ty ty = 
    case ty of 
      Types.NAME(sym, typ) => (if isSome (!typ) then (actual_ty (valOf (!typ))) else ((ErrorMsg.error 0 (" can't find a type for this name: " ^ Types.toString(ty)));Types.UNIT))
    | _ => ty

fun rm_array ty =
  case ty of
        Types.ARRAY(typ, unique) => typ
      | _ => Types.BOTTOM

(*Get last element in a list, useful for SeqExp*)
fun getLast(a::[]) = a
  | getLast(a::l) = getLast(l)
  | getLast([]) = raise Empty;

fun checkEq({exp, ty}) = case ty of 
    Types.INT => true
  | Types.RECORD(_) => true
  | Types.ARRAY(_) => true
  | Types.STRING => true
  | Types.NAME(_) => true
  | _ => false

fun getTypeFromSymbol(tenv,sym,pos) =
  case S.look(tenv, sym) of
      SOME t => t
      | NONE => (ErrorMsg.error pos (" type does not exist: "^S.name sym); Types.BOTTOM)

fun checkCycles (tenv,types) =
  let
      fun contains([],target) = false
        | contains(h::lst,target) = if h = target then true else contains(lst,target)
      fun checkInComponent([],target) = false
        | checkInComponent(com::coms,target) = if contains(com,target) then true else checkInComponent(coms,target)
      fun getComponent([],target) = NONE
        | getComponent(com::coms,target) = if contains(com,target) then SOME com else getComponent(coms,target)  
      fun addToComponent(hcom::coms,com,target) = if com = hcom then (target::com)::coms else addToComponent(coms@[hcom],com,target)
        | addToComponent(_) = [] 
      fun joinComponents(com1,com2,coms) = let 
        val toAdd = com1@com2
        fun remove(target,beg,[]) = beg
          | remove(target,beg, a::l) = if a=target then beg@l else remove(target,a::beg,l)
        val cleanedComs = remove(com2,[],remove(com1,[],coms))
        in
            toAdd::cleanedComs
        end
      fun cycles([],components) = ()
        | cycles(headtydec::tydecs,components) = 
            let val {name,ty,pos} = headtydec
                val namesym = name
            in
                case ty of
                    A.NameTy(tysym,pos') => (case getComponent(components,tysym)
                        of NONE =>
                            (case getComponent(components,namesym)
                            of NONE => cycles(tydecs,[namesym,tysym]::components)
                            | SOME com => cycles(tydecs,addToComponent(components,com,tysym))
                            )
                            
                        | SOME tycom => 
                          (case getComponent(components,namesym)
                            of NONE => cycles(tydecs,addToComponent(components,tycom,namesym))
                            | SOME namecom => if namecom=tycom then ErrorMsg.error pos ("Type cycle initiated with declaration of type "^(Symbol.name namesym)) else cycles(tydecs,joinComponents(namecom,tycom,components))
                            )
                        )
                    | _ => cycles(tydecs,components)
            end  
    in
      cycles(types,[])
    end  

fun typesEqual (a, b) = Types.check(a, b) = Types.SAM

fun typesNotEqual (a, b) = Types.check(a, b) <> Types.SAM

fun typesAssign (var, exp) = Types.check(var, exp) = Types.SAM orelse Types.check(var, exp) = Types.SUP
                                        
fun transExp(venv,tenv, level: T.level, label) =
    let fun trexp (A.OpExp{left,oper=A.PlusOp,right,pos}):expty =
                  let val l = trexp left val r = trexp right in 
                  (checkInt(l, pos);
                   checkInt(r, pos);
                   {exp=T.plus(#exp (l), #exp (r)), ty=Types.INT}) end
            | trexp (A.OpExp{left,oper=A.MinusOp,right,pos}) =
                  let val l = trexp left val r = trexp right in 
                  (checkInt(trexp left, pos);
                   checkInt(r, pos);
                   {exp=T.minus(#exp (l), #exp (r)), ty=Types.INT}) end
            | trexp (A.OpExp{left,oper=A.TimesOp,right,pos}) =
                  let val l = trexp left val r = trexp right in 
                  (checkInt(trexp left, pos);
                   checkInt(trexp right, pos);
                   {exp=T.mul(#exp (trexp left), #exp (trexp right)), ty=Types.INT}) end
            | trexp (A.OpExp{left,oper=A.DivideOp,right,pos}) =
                  let val l = trexp left val r = trexp right in 
                  (checkInt(l, pos);
                   checkInt(r, pos);
                   {exp=T.div_ir(#exp (l), #exp (r)), ty=Types.INT}) end
            | trexp (A.OpExp{left,oper=A.LtOp,right,pos}) =
                  let val l = trexp left val r = trexp right in 
                  (checkInt(trexp left, pos);
                   checkInt(trexp right, pos);
                   {exp=T.lt(#exp (l), #exp (r)), ty=Types.INT}) end
            | trexp (A.OpExp{left,oper=A.LeOp,right,pos}) =
                  let val l = trexp left val r = trexp right in 
                  (checkInt(trexp left, pos);
                   checkInt(trexp right, pos);
                   {exp=T.le(#exp (l), #exp (r)), ty=Types.INT}) end
            | trexp (A.OpExp{left,oper=A.GtOp,right,pos}) =
                  let val l = trexp left val r = trexp right in 
                  (
                    checkIntOrString(trexp left, trexp right, pos);
                    {exp=T.gt(#exp (trexp left), #exp (trexp right)), ty=Types.INT}) end
            | trexp (A.OpExp{left,oper=A.GeOp,right,pos}) =
                  let val l = trexp left val r = trexp right in 
                  (
                    checkIntOrString(l,r, pos);
                    {exp=T.ge(#exp (l), #exp (r)), ty=Types.INT}) end
            | trexp (A.OpExp{left,oper=A.EqOp,right,pos}) =
                  (let 
                    val l = trexp left
                  in
                    if (not (typesAssign(#ty l, #ty (trexp right)) andalso checkEq(l)))
                      then
                        (ErrorMsg.error pos " incompatible types";{exp=T.nil_ir(), ty=Types.BOTTOM})
                      else
                        if (#ty l = Types.STRING)
                        then
                          {exp=T.stringEq(#exp (trexp left), #exp (trexp right)), ty= Types.INT}
                        else
                        {exp=T.eq(#exp (trexp left), #exp (trexp right)), ty= Types.INT}
                  end)
            | trexp (A.OpExp{left,oper=A.NeqOp,right,pos}) =
                  (let 
                    val l = trexp left
                  in
                    if (not (typesAssign(#ty l, #ty (trexp right)) andalso checkEq(l)))
                      then
                        (ErrorMsg.error pos " incompatible types";{exp=T.nil_ir(), ty=Types.BOTTOM})
                      else
                        if (#ty l = Types.STRING)
                        then
                          {exp=T.stringNeq(#exp (trexp left), #exp (trexp right)), ty= Types.INT}
                        else
                        {exp=T.ne(#exp (trexp left), #exp (trexp right)), ty= Types.INT}
                  end)

            | trexp(A.CallExp{func = fnc, args = ar, pos = pos'}) = 
              (case S.look(venv, fnc) of
                SOME(E.FunEntry{level=decLevel, label=decLabel, formals = ar', result = res}) => 
                    matchFun(ar, ar', fnc, res, pos', venv, tenv, level, decLevel, decLabel, [])
              | NONE =>(ErrorMsg.error pos' (" function not found: "^S.name fnc);
                                {exp=T.nil_ir(),ty=Types.BOTTOM})
              | (_) =>(ErrorMsg.error pos' (" function not found: "^S.name fnc);
                                {exp=T.nil_ir(),ty=Types.BOTTOM}))
                                (* exhaustive error *)

            | trexp (A.IntExp n) = {exp=T.int_ir(n), ty=Types.INT}
            | trexp (A.RecordExp{fields=fields', typ=ty', pos=pos'}) = 
              (case S.look(tenv, ty') of
                SOME(res) => (case (actual_ty res) of
                    Types.RECORD(tys, unique) => 
                      matchTypes(fields', tys, ty', pos', [], venv, tenv, level, label)
                  | (_) => ({exp=T.nil_ir(), ty=Types.BOTTOM}))
              | NONE => (ErrorMsg.error pos' (" type not found: "^S.name ty');
                                {exp=T.nil_ir(),ty=Types.BOTTOM}))
              
            | trexp (A.ArrayExp{typ = ty, size = siz, init = ini, pos = pos'}) = 
              (case S.look(tenv, ty) of 
                SOME(res) => (case (actual_ty res) of
                  Types.ARRAY(res', uni) => (if (typesNotEqual(#ty (trexp ini), actual_ty res')) then 
                    (ErrorMsg.error pos' ("initial value of type "^(Types.toString (#ty (trexp ini)))^" inconsistent with type " ^Types.toString res')) else ();
                    {exp = T.arrayDec(#exp (trexp siz), #exp (trexp ini)), ty = Types.ARRAY(res', uni)})
                  | (_) => ({exp=T.nil_ir(), ty=Types.BOTTOM}))
              | NONE => (ErrorMsg.error pos' (" type not found: "^S.name ty);
                                {exp=T.nil_ir(),ty=Types.BOTTOM}))
            | trexp (A.StringExp(str, pos)) = {exp=T.string_ir(str), ty=Types.STRING}

            | trexp (A.LetExp{decs,body,pos}) =
                let 
                  val currentDepth = getDepth()
                  val _ = setDepth(0)
                  val ({venv=venv',tenv=tenv'}, vars) = transDecs(venv,tenv,decs, level, label, [])
                  val _ = setDepth(currentDepth)
                  val {exp, ty} = transExp(venv',tenv', level, label) body
                in 
                  {exp = T.seqExp(vars@[exp]), ty = ty}
                end
            | trexp (A.NilExp) = {exp=T.nil_ir(), ty=Types.NIL}
            | trexp (A.IfExp{test, then', else', pos}) =
            (
                let
                  val duh = (if ((typesNotEqual(#ty (trexp test), Types.INT))) then (ErrorMsg.error pos (" invalid if exp type")) else ())
                  val elseop = (case else' of
                    NONE => (if (typesNotEqual(#ty (trexp then'), Types.UNIT)) 
                      then (ErrorMsg.error pos (" invalid if then types: "^ (Types.toString(#ty (trexp then')))); NONE)
                      else NONE)
                    | SOME(elseExp) => 
                      case (#ty (trexp then'), #ty (trexp elseExp)) of
                        (Types.NIL, Types.RECORD(_)) => SOME(#exp (trexp elseExp))
                        | (Types.RECORD(_), Types.NIL) => SOME(#exp (trexp elseExp))
                        | (typeA, typeB) => 
                    (if (typesNotEqual(typeA, typeB)) 
                      then ((ErrorMsg.error pos (" invalid if then types: "^ (Types.toString(typeA)) ^ " and "^ (Types.toString(typeB)))); NONE) 
                      else SOME(#exp (trexp elseExp))))
                in
                  {exp=T.ifExp(#exp (trexp test), #exp (trexp then'), elseop), ty=(#ty (trexp then'))}
                end
                )
            | trexp (A.WhileExp{test, body, pos}) =
            (
              (if ((typesNotEqual(#ty (trexp test), Types.INT))) 
                  then (ErrorMsg.error pos (" test must be int, but is "^(Types.toString (#ty (trexp test))))) else ());
              addDepth();
              (if ((typesNotEqual(#ty (trexp body), Types.UNIT)) )
                  then (ErrorMsg.error pos (" body must be unit, but is "^(Types.toString (#ty (trexp body))))) 
                  else ());
              let
                val breakLabel = Temp.newlabel()
                val resultExp = 
                  {exp=T.whileExp(#exp (trexp test), (#exp ((transExp(venv, tenv, level, breakLabel)) body)), breakLabel), ty=Types.UNIT}
              in
                subDepth();
                resultExp
              end
            )

            | trexp (A.ForExp{var, escape, lo, hi, body, pos}) =
            (
              (if ((typesNotEqual(#ty (trexp lo), Types.INT))) 
                then (ErrorMsg.error pos (" lo must be int, but is "^(Types.toString (#ty (trexp lo))))) else ());
              (if ((typesNotEqual(#ty (trexp hi), Types.INT))) 
                then (ErrorMsg.error pos (" hi must be int, but is "^(Types.toString (#ty (trexp hi))))) else ());
              addDepth();
              let
                val ac = T.allocLocal level FOR_ESCAPE
                val newEnv = S.enter(venv, var, E.VarEntry{
                  access=ac,
                  ty=Types.INT, 
                  assignable=false})
                val breakLabel = Temp.newlabel()
                val countVar = T.simpleVar(ac, level)
                val bodyCheck = 
                  (if ((typesNotEqual(#ty (transExp(newEnv, tenv, level, breakLabel) body), Types.UNIT))) then (ErrorMsg.error pos (" body must be unit, but is "^(Types.toString (#ty (trexp body))))) else ());
                val resultExp = {exp=T.forExp(countVar, #exp (trexp lo), #exp (trexp hi), #exp ((transExp(newEnv, tenv, level, breakLabel)) (body)), breakLabel), ty=Types.UNIT}
              in
                subDepth();
                resultExp
              end
            )

            | trexp(A.BreakExp pos) =
            (
              (
                if !depth = 0
                then (ErrorMsg.error pos (" break not in for or while loop"))
                else ()
              );
              {exp=T.breakExp(label), ty=Types.UNIT}
            )

            | trexp(A.AssignExp({var, exp, pos})) =
              let
                fun getSymbol var = 
                  case var of
                    A.SimpleVar(sym, _) => S.look(venv, sym)
                    | A.FieldVar(var, _, _) => getSymbol(var)
                    | A.SubscriptVar(var, _, _) => getSymbol(var)
                fun assignable var = 
                  case getSymbol(var) of
                    SOME(Env.VarEntry({access, ty, assignable})) => if assignable then () else ErrorMsg.error pos " not assignable because it's an iterator"
                    | _ => (ErrorMsg.error pos " can't assign to anything other than a variable")
              in
              (
                assignable(var);
                (if ((typesNotAssign(#ty (trvar var), #ty (trexp exp)))) then 
                  (ErrorMsg.error pos (" type "^(Types.toString (#ty (trexp exp))) ^" not assignable to variable of type "^(Types.toString (#ty (trvar var))))) 
                else ());
                {exp=T.assign(#exp (trvar var), #exp (trexp exp)), ty=Types.UNIT}
              )
              end
            | trexp(A.SeqExp(lst)) = 
                (
                  let
                    val resl = map #exp (map trexp (map #1 lst))
                    val t = case lst of 
                      [] => Types.UNIT
                    |  _ => (#ty (getLast(map trexp (map #1 lst))))
                    val e = case resl of
                      [] => T.nil_ir()
                    | _  => T.seqExp(resl)
                  in
                    {exp=e, ty=t}
                  end
                )
            | trexp (A.VarExp(var)) = trvar var

        and trvar(A.SimpleVar(id,pos)) =
                (case S.look(venv,id) of
                      SOME(E.VarEntry{access, ty:Types.ty, assignable:bool}) =>
                        {exp=T.simpleVar(access, level), ty=actual_ty ty}
                    | NONE => (ErrorMsg.error pos (" undefined variable "^S.name id);
                                {exp=T.nil_ir(),ty=Types.BOTTOM})
                    | (_) => (ErrorMsg.error pos (" undefined variable "^S.name id);
                                {exp=T.nil_ir(),ty=Types.BOTTOM}))
                                (* exhaustive error *)
          | trvar(A.FieldVar(var, sym, pos)) =
            let 
              val full_fields =
                (case actual_ty (#ty (trvar(var))) of
                    Types.RECORD(fields, unique) => fields
                  | (_) => []
                )

              fun inRecord(var, sym, fields, pos, venv, tenv, level, label) = 
                  case fields of 
                    [] => (ErrorMsg.error pos (" field name not in record: " ^ S.name sym); 
                      {exp=T.nil_ir(), ty=Types.BOTTOM})
                  | ((asym, atyp)::l) => 
                    if 
                      asym = sym 
                    then 
                      (
                      {exp=T.fieldVar(#exp (trvar var), sym, full_fields), ty=actual_ty atyp} 
                      )
                    else 
                      inRecord(var, sym, l, pos, venv, tenv, level, label)
            in
                (case actual_ty (#ty (trvar(var))) of
                      Types.RECORD(fields, unique) => (inRecord(var, sym, fields, pos, venv, tenv, level, label))
                    | _ => (ErrorMsg.error pos (" bad record access: "^S.name sym); 
                                {exp=T.nil_ir(), ty=Types.BOTTOM}))
            end
          | trvar(A.SubscriptVar(var, exp, pos)) =
          (
              (case actual_ty (#ty (trvar(var))) of
                Types.ARRAY(ty, unique) => (checkInt(trexp exp, pos); 
                  {exp=T.subscriptVar(#exp (trvar var), #exp (trexp exp)), ty= actual_ty (rm_array (actual_ty (#ty (trvar(var)))))})
              | _ => (ErrorMsg.error pos (" bad array access: "); 
                                {exp=T.nil_ir(), ty=Types.BOTTOM}))
            )

    in
        trexp
    end


and transTy(tenv, A.NameTy(sym, pos)) = getTypeFromSymbol(tenv,sym,pos)
    | transTy(tenv, A.RecordTy(fields)) = 
      let
        fun recordFields tenv ({name,escape,typ,pos},acc) = acc @ [(name,getTypeFromSymbol(tenv,typ,pos))]
      in
        Types.RECORD(foldl (recordFields tenv) [] fields, ref ())
      end
    | transTy(tenv, A.ArrayTy(sym,pos)) = Types.ARRAY(getTypeFromSymbol(tenv,sym,pos), ref ())
        
and transDec (venv, tenv, A.VarDec{name=var, escape=esc, typ=NONE, init=init', pos=pos'}, level, label) =
        let 
          val {exp,ty} = (transExp(venv, tenv, level, label)) init'
          val ac = (T.allocLocal level (!esc))
        in (if (actual_ty ty = Types.NIL) then (ErrorMsg.error pos' ("cannot assign nil value to an untyped variable")) else ();
          ({tenv=tenv,venv = S.enter(venv, var, E.VarEntry{
            access=ac,
            ty=ty, 
            assignable=true})}, SOME(T.assign(T.simpleVar(ac, level), #exp ((transExp(venv, tenv, level, label)) init')))))
        end
    | transDec (venv, tenv, A.VarDec{name=var, escape=esc, typ=SOME atyp, init=init', pos=pos'}, level, label) =
        let val {exp,ty} = transExp(venv, tenv, level, label) init'
            val (sym,pos) = atyp
            val typ = getTypeFromSymbol(tenv,sym,pos')
            val ac = (T.allocLocal level (!esc))
        in (
        if 
          typesNotAssign(actual_ty typ, ty) 
        then 
          (ErrorMsg.error pos' (" variable declared with type "^(Types.toString (actual_ty typ)^" not equal to right hand side type "^(Types.toString ty)))) 
        else ();
        ({tenv=tenv,venv = S.enter(venv, var, E.VarEntry{
          access=ac,
          ty=actual_ty typ, 
          assignable=true})}, SOME(T.assign(T.simpleVar(ac, level), #exp (transExp(venv, tenv, level, label) init')))))
        end        
    | transDec (venv, tenv, A.TypeDec(tdecs), level, label) = 
      let
        fun inList a b = if a=b then true else false
        fun do_headers({name=name, ty=ty, pos=pos}, (tcurr,namelist)) = 

        (if (List.exists (inList(name)) namelist) then 
          (ErrorMsg.error pos ("duplicate mutually recursive type created with name "^(S.name name))) else ();
          (S.enter(tcurr, name, Types.NAME(name, ref NONE )), namelist@[name]))

        val temp_tenv_namelist_pair = foldl do_headers (tenv,[]) tdecs
        val temp_tenv = case temp_tenv_namelist_pair of
          (res, _) => res

        fun do_body({name=name, ty=ty, pos=pos}, tcurr') = (
          case S.look(tcurr', name) of SOME(Types.NAME(n, realty)) => realty := SOME(transTy(tcurr', ty)); tcurr')
        val final_tenv = foldl do_body temp_tenv tdecs
        val _ = checkCycles(final_tenv,tdecs)
      in
        ({venv=venv, tenv=final_tenv}, NONE)
      end
    | transDec (venv, tenv, A.FunctionDec(fn_list), level, label) =
        let 
          fun inList a b = if a=b then true else false
          fun getEscapeHelper {name=my_name, escape=my_escape, typ=my_typ} = !my_escape
          fun getEscape params = map getEscapeHelper params
          fun setupFn (venv, tenv, {name,params,body,pos,result=rt_op}) =
            let 
                val result_ty = case rt_op of 
                  SOME(rt,pos2) => if isSome (S.look(tenv, rt)) then valOf (S.look(tenv, rt)) else (ErrorMsg.error pos " result type doesn't exist"; Types.BOTTOM)
                | NONE => Types.UNIT
                (*Do the body later, now we just put in the header*)
                fun transparam{name,escape,typ,pos} =
                  case S.look(tenv,typ)
                  of SOME t => {name=name,escape=escape,typ=t}
                      | NONE => (ErrorMsg.error pos (" type does not exist: "^S.name typ);{name=name,escape=escape,typ=Types.BOTTOM})
                val params' = map transparam params
                val lb = Temp.newlabel()
                val venv' = S.enter(venv,name,
                  E.FunEntry{
                    level=T.newLevel {
                      parent=level, 
                      name=lb,
                      formals = getEscape params'},
                    label=lb,
                    formals=map #typ params',
                    result=result_ty})   
            in 
              (venv', body, params', result_ty, pos)
            end 
          fun enterfn(this_fn, (vcurr, (eval_list, namelist))) = case setupFn (vcurr, tenv, this_fn) of
            (vtemp, body, params, rt_ty, pos) => ( if (List.exists (inList(#name (this_fn))) namelist) then
              (ErrorMsg.error pos ("duplicate mutually recursive function created with name "^(S.name (#name (this_fn))))) else ();
            (vtemp, (eval_list@[(body, params, rt_ty, pos)], namelist@[#name (this_fn)])))
          val env_eval_name_triple = foldl enterfn (venv,([],[])) fn_list
          val new_venv = case env_eval_name_triple of
            (nvenv, blah) => nvenv
          val eval_name_pair_list = case env_eval_name_triple of
            (blah, eval) => eval
          fun merge(item, (res, b::l)) = (res@[(item,b)],l)
            | merge(_) = ([],[]) (* exhaustive error *)
          val merged_list = #1 (foldl merge ([], #2 eval_name_pair_list) (#1 eval_name_pair_list))
         (*Now we do all the bodies*)
          fun check_fn(((body, params, rt_ty, pos), name), venv') =
            let
              val newLevel = 
                (
                  case S.look(venv', name) of
                    SOME(E.FunEntry({level=my_level, label=_, formals=_, result=_})) => (my_level)
                    | _ => T.newLevel {parent=T.outermost, name=Temp.newlabel(), formals=[]}
                )
              val actual_rt_ty = actual_ty rt_ty
              val translate_formals = rev(T.formals newLevel)
              fun enterparam({name,escape, typ}, (venv, i)) = 
                let 
                  val actual_param_ty = actual_ty typ
                in
                  (S.enter(venv,name,E.VarEntry{
                    access = List.nth(translate_formals, i),
                    ty=actual_param_ty, 
                    assignable=true}),
                    i+1)
                end
              val venv'' = foldl enterparam (venv', 0) params
              val {exp,ty} = transExp(#1 venv'',tenv, newLevel, label) body
              val temp = 
                if 
                  typesNotEqual(actual_rt_ty, ty) 
                then 
                  (ErrorMsg.error pos (" function body type "^(Types.toString ty) ^" not equal to return type "^(Types.toString (actual_rt_ty)))) 
                else ()

            in
              T.procEntryExit {level=newLevel, body=exp};
              temp;
              venv'
            end
        in
          (foldl check_fn new_venv merged_list;({venv=new_venv, tenv=tenv}, NONE))
        end
    
    
and transDecs (venv,tenv,[], level, label, vars: T.exp list) = ({venv=venv,tenv=tenv}, vars)
  | transDecs(venv,tenv,dec::decs, level, label, vars: T.exp list) = 
    let 
      val ({venv=venv',tenv=tenv'}, var) = transDec(venv,tenv,dec, level, label)
    in 
      case var of 
        SOME(res) => transDecs(venv',tenv',decs, level, label, vars@[res])
      | NONE => transDecs(venv',tenv',decs, level, label, vars)
    end

and matchFun(ar, ar', fnc, res, pos', venv, tenv, level, decLevel, label, expArgs) = 
  case ar of
    [] => 
      (
        case ar' of
            [] => {exp=T.callExp(label, level, decLevel, expArgs), ty = actual_ty res}
          | _ => (ErrorMsg.error pos' ("args do not match in fn call: " ^S.name fnc); {exp=T.nil_ir(), ty=Types.BOTTOM})
      )
  | (a::l) => (case ar' of
      (b::li) => 
          if 
            typesEqual( #ty (transExp(venv, tenv, level, label) a), actual_ty b) 
          then 
            matchFun(l, li, fnc, res, pos', venv, tenv, level, decLevel, label, expArgs @ [(#exp ((transExp(venv, tenv, level, label) a)))])
          else 
            (ErrorMsg.error pos' ("args do not match in fn call: " ^S.name fnc); {exp=T.nil_ir(), ty=Types.BOTTOM})
    | [] => (ErrorMsg.error pos' ("args do not match in fn call: " ^S.name fnc); {exp=T.nil_ir(), ty=Types.BOTTOM})
              )      
  
and matchTypes(fields, tys, recTy, pos, exps, venv, tenv, level, label) = 
    case fields of
    [] => (case tys of
      [] => {exp=T.recordDec(exps), ty=case S.look(tenv, recTy) of SOME(res) => actual_ty res | NONE => Types.BOTTOM}
    | ((sym, ty')::l) => (ErrorMsg.error pos (" fields do not match type "^S.name sym); {exp=T.nil_ir(), ty=Types.BOTTOM})
          )
  | ((ty, exp, posf)::l) => (case tys of
      ((sym, ty')::li) => if ty = sym 
        then matchTypes(l, li, recTy, pos, exps@[(#exp ((transExp(venv, tenv, level, label) exp)))], venv, tenv, level, label) 
        else (ErrorMsg.error pos (" fields do not match type "^S.name sym); {exp=T.nil_ir(), ty=Types.BOTTOM})
    | [] => (ErrorMsg.error pos (" fields do not match type "); {exp=T.nil_ir(), ty=Types.BOTTOM}))
                          

fun transProg(exp:Absyn.exp) = 
  let
    val outerLabel = Temp.namedlabel "tig_main"
    val outerLevel = T.newLevel {parent=T.outermost, name=outerLabel, formals=[]}
    val mainExp = #exp (transExp(Env.base_venv,Env.base_tenv, outerLevel, outerLabel) exp )
  in
    (* call T *)
    T.procEntryExit {level=outerLevel, body=mainExp};
    (* get result from translate *)
    T.getResult()
  end

fun printAst(exp:Absyn.exp) = 
  let
    val blah = FindEscape.findEscape exp
    val printed = PrintAbsyn.print(TextIO.stdOut, exp)
  in
    ()
  end

end
