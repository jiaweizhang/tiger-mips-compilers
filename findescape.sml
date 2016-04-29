structure FindEscape : sig 

	      val findEscape : Absyn.exp -> unit 
	      val resetEscapes : unit -> unit 
	      val getEscapes : unit -> (bool ref) list ref

	  end 
=

struct

structure A = Absyn
structure E = Env
structure S = Symbol

type depth = int
type escEnv = (depth * bool ref) Symbol.table

val escapes = ref [] : (bool ref) list ref

fun traverseVar(env:escEnv, d:depth, s:Absyn.var): unit = 
  let 
      fun trvar (A.SimpleVar(symbol, pos)) = 
        (
          (case S.look(env, symbol) of
               SOME(foundD, escapes) => if
					   foundD >= d
                                       then 
					   ()
                                       else
					   (escapes := true)
             | _ => () (* not found *) )
        )
	| trvar (A.FieldVar(var, symbol, pos)) = trvar(var)
	| trvar (A.SubscriptVar(var, exp, pos)) = (trvar (var); traverseExp(env, d, exp))
  in
      trvar s
  end

and traverseExp(env:escEnv, d:depth, s:Absyn.exp): unit = 
    let
	fun trexp (A.VarExp(var)) = traverseVar(env, d, var)
	  | trexp (A.NilExp) = ()
	  | trexp (A.IntExp(int)) = ()
	  | trexp (A.StringExp(string, pos)) = ()
	  | trexp (A.CallExp({func, args, pos})) = (map trexp args; ())
	  | trexp (A.OpExp({left, oper, right, pos})) = (trexp left; trexp right)
	  | trexp (A.RecordExp({fields, typ, pos})) = 
            let 
		fun getExp (symbol, exp, pos) = exp
		val exps = map getExp fields
            in
		(map trexp exps; ())
            end
	  | trexp (A.SeqExp(expList)) =
            let
		fun getExp (exp, pos) = exp
		val exps = map getExp expList
            in
		(map trexp exps; ())
            end
	  | trexp (A.AssignExp({var, exp, pos})) = (traverseVar(env, d, var); trexp exp)
	  | trexp (A.IfExp({test, then', else', pos})) = 
            (
              trexp(test);
              trexp(then');
              case else' of
		  SOME(elseExp) => trexp(elseExp)
		| _ => ()
            )
	  | trexp (A.WhileExp({test, body, pos})) = 
            (
              trexp(test);
              trexp(body)
            )
	  | trexp (A.ForExp({var, escape, lo, hi, body, pos})) = 
            let
		val tmpEnv = S.enter(env, var, (d, escape))
            in
		traverseExp(tmpEnv, d, lo);
		traverseExp(tmpEnv, d, hi);
		traverseExp(tmpEnv, d, body)
            end
	  | trexp (A.BreakExp(pos)) = ()
	  | trexp (A.LetExp({decs, body, pos})) =
            let
		val tmpEnv = traverseDecs(env, d, decs)
            in
		traverseExp(tmpEnv, d, body)
            end
	  | trexp (A.ArrayExp({typ, size, init, pos})) =
            (
              trexp(size);
              trexp(init)
            )
    in
	trexp s
    end

and traverseDecs(env, d, s: Absyn.dec list): escEnv = 
    let 
	fun trdec (A.FunctionDec(fundecList), tmpEnv) =
          let 
              val initEnv = tmpEnv
              (* iterate through fundecs and add all params to env *)
              fun addToEnv ({name, escape, typ, pos}, fun_env) = 
                (escapes := escape::(!escapes);S.enter(fun_env, name, (d+1, escape)))
              fun processFundec ({name, params, result, body, pos}) =
                let
                    val newEnv = foldl addToEnv tmpEnv params
                in
                    traverseExp(newEnv, d+1, body)
                end
          in
              map processFundec fundecList;
              initEnv
          end
          | trdec (A.VarDec{name, escape, typ, init, pos}, tmpEnv) = 
            let
		val newEnv = S.enter(tmpEnv, name, (d, escape))
            in
		escapes := escape::(!escapes);
		traverseExp(newEnv, d, init);
		newEnv
            end
          | trdec (A.TypeDec(tydecList), tmpEnv) = tmpEnv
    in
        foldl trdec env s
    end

fun findEscape(prog: Absyn.exp) : unit = traverseExp(S.empty, 0, prog)

(* reset only once *)
fun resetEscapes () = escapes := []
fun getEscapes () = escapes
end
