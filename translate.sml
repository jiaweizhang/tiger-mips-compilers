structure F = MipsFrame

signature TRANSLATE =
sig
	type level
	type access
	type exp

	val outermost : level
	val newLevel : {parent: level, name: Temp.label, formals: bool list} -> level
	val formals: level -> access list
	val allocLocal: level -> bool -> access

	(*Functions to translate into IR*)
	val plus: exp * exp -> exp
	val minus: exp * exp -> exp
	val mul: exp * exp -> exp
	val div_ir: exp * exp -> exp
	val lt: exp * exp -> exp
	val le: exp * exp -> exp
	val gt: exp * exp -> exp
	val ge: exp * exp -> exp
	val eq: exp * exp -> exp
	val ne: exp * exp -> exp
	val stringEq: exp * exp -> exp
	val stringNeq: exp * exp -> exp

	val ifExp: exp * exp * exp option -> exp
	val whileExp: exp * exp * Temp.label -> exp
	val forExp: exp * exp * exp * exp * Temp.label -> exp
	val breakExp: Temp.label -> exp

	val seqExp: exp list -> exp
	val callExp: Temp.label * level * level * (exp list) -> exp

  val assign: exp * exp -> exp 
  val nil_ir: unit -> exp
  val int_ir: int -> exp
  val string_ir: string -> exp

	val simpleVar: access * level -> exp
	val subscriptVar: exp * exp -> exp
	val fieldVar: exp * Symbol.symbol * (Symbol.symbol * Types.ty) list -> exp

	val arrayDec: exp * exp -> exp
	val recordDec: exp list -> exp

  val emptyFragList : unit -> unit
  val procEntryExit : {level: level, body: exp} -> unit
  val getResult : unit -> F.frag list
end

structure Translate : TRANSLATE = 
struct 
  structure T = Tree

  val fragList = ref [] : F.frag list ref

	val error = Temp.newlabel()

	datatype level = FIRSTLEVEL
	               | LEVEL of {parent: level, frame: F.frame, unique: unit ref}

    fun plevel(level) = (print (case level of 
                        LEVEL{unique=_, frame=f, parent=_} => (Symbol.name (#name f))
                      | FIRSTLEVEL => "first"); print "\n")
                   
	val outermost = FIRSTLEVEL
	type access = level * F.access

	datatype exp =
		  Ex of Tree.exp
		| Nx of Tree.stm
		| Cx of Temp.label * Temp.label -> Tree.stm

	fun   unEx (Ex e) = e
		| unEx (Cx genstm) =
			let val r = Temp.newtemp()
				val t = Temp.newlabel() and f = Temp.newlabel()
			in
				T.ESEQ(T.SEQ[
						T.MOVE(T.TEMP r, T.CONST 1),
						genstm(t, f),
						T.LABEL f,
						T.MOVE(T.TEMP r, T.CONST 0),
						T.LABEL t],
					T.TEMP r)
			end
		| unEx (Nx s) = T.ESEQ(s, T.CONST 0)

	fun   unCx (Cx c) = c
		| unCx (Ex e) = 
      (
        case e of
			      T.CONST(0) => (fn(t, f) => T.JUMP(T.NAME(f),[f]))
    		  |	T.CONST(1) => (fn(t,f) => T.JUMP(T.NAME(t),[t]))
    		  | _ => (fn(t,f) => T.CJUMP(T.EQ, e, T.CONST(1), t, f))
      )
		| unCx (Nx _ ) = (ErrorMsg.error 999 " You tryna unCx an Nx"; (fn(t, f) => Tree.LABEL(Temp.newlabel())))

	fun   unNx (Ex e) = T.EXP(e)
		| unNx (Nx n) = n
		| unNx (c) = unNx (Ex (unEx (c)))

  fun newLevel{parent=parent', name=name', formals=formals'} = 
    (
    LEVEL({ 
      parent = parent', 
      frame=F.newFrame{name=name', formals=true::formals'}, 
      unique = ref ()})
    )

  fun formals (LEVEL({frame=fr, unique=u, parent = p})) = 
  		let
  			val l = F.formals fr
  			fun makeRes (item, li) = (LEVEL({frame=fr,parent=p,unique=u}), item)::li
  		in
  			foldl makeRes [] (List.tl l)
  		end
  	| formals(FIRSTLEVEL) = []

  fun allocLocal lev esc = case lev of 
  	LEVEL({parent=_, frame=fr, unique=_}) => (lev, F.allocLocal fr esc)
  | FIRSTLEVEL => (ErrorMsg.error 999 " impossible"; (outermost, (F.allocLocal (F.newFrame {name=Temp.newlabel(), formals=[]}) esc)))

  (*Translate IR*)

  (* constant folding *)
  fun plus(Ex(T.CONST left), Ex(T.CONST right)) = Ex(T.CONST (left+right)) 
    | plus(left, Ex(T.CONST 0)) = left
    | plus(Ex(T.CONST(0)), right) = right
    | plus(left, right) = Ex(T.BINOP(T.PLUS, unEx(left), unEx(right)))

  (* constant folding *)
  fun minus(Ex(T.CONST left), Ex(T.CONST right)) = Ex(T.CONST (left-right)) 
    | minus(left, Ex(T.CONST 0)) = left
    | minus(left, right) = Ex(T.BINOP(T.MINUS, unEx(left), unEx(right)))

  (* constant folding *)
  fun mul(Ex(T.CONST left), Ex(T.CONST right)) = Ex(T.CONST (left*right)) 
    | mul(left, Ex(T.CONST 0)) = Ex(T.CONST 0)
    | mul(Ex(T.CONST 0), right) = Ex(T.CONST 0)
    | mul(left, Ex(T.CONST 1)) = left
    | mul(Ex(T.CONST 1), right) = right
    | mul(left, right) = Ex(T.BINOP(T.MUL, unEx(left), unEx(right)))

  (* constant folding *)
  fun div_ir(Ex(T.CONST left), Ex(T.CONST right)) = Ex(T.CONST (left div right)) 
    | div_ir(Ex(T.CONST 0), right) = Ex(T.CONST 0)
    | div_ir(left, Ex(T.CONST 1)) = left
    | div_ir(left, right) = Ex(T.BINOP(T.DIV, unEx(left), unEx(right)))

  fun lt(left, right) = 
  	let
  		fun check(t,f) = T.CJUMP(T.LT, unEx(left), unEx(right), t, f)
  	in
  		Cx(check)
  	end

  fun le(left, right) = 
  	let
  		fun check(t,f) = T.CJUMP(T.LE, unEx(left), unEx(right), t, f)
  	in
  		Cx(check)
  	end

  fun gt(left, right) = 
  	let
  		fun check(t,f) = T.CJUMP(T.GT, unEx(left), unEx(right), t, f)
  	in
  		Cx(check)
  	end

  fun ge(left, right) = 
  	let
  		fun check(t,f) = T.CJUMP(T.GE, unEx(left), unEx(right), t, f)
  	in
  		Cx(check)
  	end

  fun eq(left, right) = 
  	let
  		fun check(t,f) = T.CJUMP(T.EQ, unEx(left), unEx(right), t, f)
  	in
  		Cx(check)
  	end

  fun ne(left, right) = 
  	let
  		fun check(t,f) = T.CJUMP(T.NE, unEx(left), unEx(right), t, f)
  	in
  		Cx(check)
  	end

  fun assign(left, right) = 
    let
      fun validateExp (T.MEM exp) = T.MEM exp
        | validateExp (T.TEMP temp) = T.TEMP temp
        | validateExp (T.ESEQ (stm, tmp_exp as T.MEM (_))) = T.ESEQ (stm, tmp_exp)
        | validateExp (T.ESEQ (stm, tmp_exp as T.TEMP (_))) = T.ESEQ(stm, tmp_exp)
        | validateExp (_) = (ErrorMsg.error 999 " bad assign destination"; T.TEMP (Temp.newtemp()))
    in
      Nx (T.MOVE(validateExp (unEx left), unEx right))
    end

  fun nil_ir () = Ex (T.CONST (0))

  fun int_ir (x) = Ex (T.CONST (x))

  fun string_ir (lit) =
    let
      fun isSameLabel (fragment) =
        case fragment of
            F.STRING(my_lab, my_lit) => String.compare (lit, my_lit) = EQUAL
          | F.PROC(_) => false
      val lab = 
        case (List.find isSameLabel (!fragList)) of
            SOME(F.STRING(my_lab, my_lit)) => my_lab
          | _ =>  let 
                    val newLab = Temp.newlabel()
                  in
                    fragList := (F.STRING(newLab, lit))::(!fragList);
                    newLab
                  end
    in
      Ex (T.NAME(lab))
    end

    
  (* made extCall take array of exp instead of exp*exp *)
  fun stringEq(left, right) =
  	let
  	 fun check(t,f) = T.CJUMP(T.NE, F.extCall("tig_stringEqual", [unEx(left), (unEx(right))]), T.CONST(0), t, f)
  	in
  		Cx(check)
  	end

  fun stringNeq(left, right) =
  	let
  	 fun check(t,f) = T.CJUMP(T.EQ, F.extCall("tig_stringEqual", [unEx(left), (unEx(right))]), T.CONST(0), t, f)
  	in
  		Cx(check)
  	end

  fun ifExp(test, t, f) =
  	let
  		val tl = Temp.newlabel() and fl = Temp.newlabel() and zl = Temp.newlabel() and el = Temp.newlabel()
      val tmp = Temp.newtemp()
  		val check = case f of
  			 SOME(res) => T.SEQ[ (unCx(test) (zl,fl)),
  					T.LABEL(zl),
  					T.MOVE(T.TEMP(tmp), unEx(t)),
  					T.JUMP(T.NAME(el), [el]),
  					T.LABEL(fl),
  					T.MOVE(T.TEMP(tmp), unEx(res)),
  					T.LABEL(el)]
  			| NONE => T.SEQ[ (unCx(test) (tl, fl)),
  					T.LABEL(tl),
  					T.MOVE(T.TEMP(tmp), unEx(t)),
  					T.LABEL(fl)]
  	in
  		Ex(T.ESEQ(check, T.TEMP(tmp)))
  	end

  fun whileExp(test, body, breaklabel) =
  	let
  		val beg = Temp.newlabel() and tst = Temp.newlabel()
  		val loop = T.SEQ[ T.JUMP(T.NAME(tst), [tst]),
  						T.LABEL(beg),
  						unNx(body),
  						T.LABEL(tst),
  						unCx(test) (beg, breaklabel),
  						T.LABEL(breaklabel)]
  	in
  		Nx(loop)
  	end

  fun forExp(var, lo, hi, body, breaklabel) = 
  	let
  		val tst = Temp.newlabel() and beg = Temp.newlabel() and pass = Temp.newlabel()
  		val loop = T.SEQ[ T.MOVE(unEx(var), unEx(lo)),
  							T.CJUMP(T.LE, unEx(lo), unEx(hi), beg, breaklabel),
  							T.LABEL(beg),
  								unNx(body),
  								T.CJUMP(T.LT, unEx(var), unEx(hi), pass, breaklabel),
  							T.LABEL(pass),
  								T.MOVE(unEx(var), T.BINOP(T.PLUS, unEx(var), T.CONST(1))),
  								T.JUMP(T.NAME(beg), [beg]),
  							T.LABEL(breaklabel)]
  	in
  		Nx(loop)
  	end

  fun breakExp(breaklabel) = Nx(T.JUMP(T.NAME(breaklabel), [breaklabel]))

  fun seqExp(lst) = 
    let
      fun makeRes(lst, res) = case lst of

        [] => T.CONST(~7) (*We should never get here*)
        | (a::[]) => (
            case res of
                [single] => (T.ESEQ(single, unEx(a)))
              | (multiple) => T.ESEQ(T.SEQ(multiple), unEx(a)))
        | (a::l) => makeRes(l, res@[unNx(a)])
      val retVal = case lst of 
          [single] => unEx(single)
        | (multiple) => makeRes(multiple, [])
  	in
  		Ex(retVal)
  	end
    

  fun getLink(currLev:level, decLev:level) = case decLev of
  	FIRSTLEVEL => T.CONST(~2) (*Badzo*)
  |	LEVEL({parent=p, frame=_, unique=_}) => 
  		(case p of LEVEL({parent=_, frame=_, unique=u}) => 
  			(case currLev of LEVEL({parent=pc, frame=fc, unique = uc}) =>
  			if (uc = u) 
  				then T.TEMP(F.FP)
  				else F.exp ((List.hd (F.formals fc)), (getLink(pc, decLev)))
  			| FIRSTLEVEL => T.CONST(~3) (*Uh-oh*))
  		| FIRSTLEVEL => T.CONST(~4) (*Uh-oh*))

  fun callExp(lab, callLev, decLev, args) = 
  	let
      val theBool = String.size(Symbol.name lab)>=4 andalso (String.compare(String.substring((Symbol.name lab), 0, 4), "tig_") = EQUAL)
  		val link = 
        case theBool of
            true => []
          | false => [getLink(callLev, decLev)]
  	in
  		Ex(T.CALL(T.NAME(lab), link @ (map unEx args)))
  	end

  fun follow x = case x of
      (fac, FIRSTLEVEL, _, link) => (ErrorMsg.error 666 " voodoo error"; link) 
    | (fac, _, FIRSTLEVEL, link) => (ErrorMsg.error 666 " voodoo error2"; link) 
    | (fac, early as LEVEL{unique=u, frame=f, parent=p}, LEVEL{unique=ua, frame=fa, parent=pa}, link) =>
      if 
        u=ua
      then
        link
      else 
        follow (fac, early, pa, T.MEM(follow (fac, early, pa, link)))

  fun simpleVar((early, frac), late) = 
    Ex(F.exp(frac, follow(frac, early, late, T.TEMP(F.FP))))

  fun subscriptVar(var, index) = 
  	let 
  		val size = Temp.newtemp() and res = Temp.newtemp()
  		val t = Temp.newlabel() and z = Temp.newlabel() and n = Temp.newlabel() and f = Temp.newlabel()
      val var' = Temp.newtemp()
      val index' = Temp.newtemp()
      val error = Temp.newlabel()
  	in
  		Ex(T.ESEQ(T.SEQ[
          T.MOVE(T.TEMP var', unEx var),
          T.MOVE(T.TEMP index', unEx index),
  				T.MOVE(T.TEMP(size), T.MEM(T.BINOP(T.MINUS, T.TEMP var', T.CONST(F.wordSize)))),
  				T.CJUMP(T.LT, T.TEMP index', T.TEMP(size), z, error), (*Check index less than size*)
  				T.LABEL(z),
  					T.CJUMP(T.GE, T.TEMP index', T.CONST(0), t, error), (*Check index greater than zero*)
          T.LABEL error,
            T.EXP(T.CALL(T.NAME (Temp.namedlabel "tig_exit"), [T.CONST 0])),
  				T.LABEL(t)], 
  			T.MEM(T.BINOP(T.PLUS, T.TEMP var', T.BINOP(T.MUL, T.TEMP index', T.CONST(F.wordSize))))))
  	end

  fun fieldVar(var, sym, fields) =
  	let 
  		fun findField((s, _), (res, count)) = 
  			if sym = s then (count, count + 1) else (0, count + 1)
  		val index = #1 (foldl findField (0, 0) fields)
  	in
  		Ex(T.MEM(T.BINOP(
            T.PLUS,
            T.CONST(index * F.wordSize),
            unEx (var))))
  	end

  fun arrayDec(siz, ini) = 
  	let
  		val tmp = Temp.newtemp()
  		val newsize = T.BINOP(T.PLUS, unEx(siz), T.CONST(1)) (*Put the size first in the array*)
  	in
  		Ex(T.ESEQ(T.SEQ[
  				T.MOVE(T.TEMP(tmp), F.extCall("tig_initArray", [newsize, unEx(ini)])), (* added brackets to make into list *)
  				T.MOVE(T.MEM(T.TEMP(tmp)),unEx(siz)), (*Here's the size for bounds checking*)
  				T.MOVE(T.TEMP(tmp), T.BINOP(T.PLUS, T.TEMP(tmp), T.CONST(F.wordSize)))], (*Return one address higher -- where the values start*)
  			T.TEMP(tmp)))
  	end

  fun recordDec(exps) = 
  	let
  		val tmp = Temp.newtemp()

      val initRecord = [T.MOVE(
          T.TEMP(tmp), 
          F.extCall("tig_allocRecord", [T.CONST(List.length(exps)* F.wordSize)]))]

  		fun fillNext(ex, moves) = 
          moves @ [T.MOVE (
              		  T.MEM(
                      T.BINOP(
                        T.PLUS, 
                        T.TEMP(tmp), 
                        T.CONST((List.length(moves) - 1) * F.wordSize))), (* haxx *) 
              		  unEx(ex))]
  		val allMoves = foldl fillNext initRecord exps 
  		(*First move is the intRecord*)
  		(*All moves after that are for each field*)
  	in
  		Ex(T.ESEQ(T.SEQ(allMoves),
  			T.TEMP(tmp)))
  	end

  fun emptyFragList () = fragList := []

  fun procEntryExit {level=my_level, body=my_body} = 
    let
      val real_frame = 
        case my_level of
            FIRSTLEVEL => F.newFrame ({name=Temp.newlabel(), formals=[]})
          | LEVEL ({parent, frame, unique}) => frame
          
      val proc_body = T.MOVE(T.TEMP(F.RV), unEx (my_body))
      val result_body = F.procEntryExit1(real_frame, proc_body)
    in
      fragList := F.PROC({body=result_body, frame=real_frame})::(!fragList)
    end

  fun getResult () = !fragList

end