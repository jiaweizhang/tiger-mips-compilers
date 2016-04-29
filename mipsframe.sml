structure MipsFrame : FRAME = 
struct
  structure T = Tree

	datatype access = InFrame of int | InReg of Temp.temp

	type frame = {
    name: Temp.label, 
    formals: access list,
    locals: int ref,
    offset: int ref}

  val wordSize = 4
  type register = string

  (* don't be printing the sequences actually because certain SPIM may have parse error *)
  fun escape #"\t" = "\\t"
    | escape #"\n" = "\\n"
    | escape c = Char.toString(c)

  fun toString(lab, s) = 
    (Symbol.name (lab))^":\n .word "^Int.toString(String.size(s))^"\n .ascii \""^(String.translate escape s)^ "\"\n"

  fun getTemps(0) = [] 
    | getTemps(i) = Temp.newtemp()::getTemps(i-1)
  val specialregs = getTemps(5)
  val argregs = getTemps(4)
  val calleesaves = getTemps(8)
  val callersaves = getTemps(10)
  val all_regs = (specialregs@argregs@callersaves@calleesaves)
  val newcallersaves = callersaves@specialregs@argregs
  val FP = List.nth(specialregs, 1)
  val RV = List.nth(specialregs, 0)
  
  fun findIndex(v,lst) =
    let
        fun findHelper(v,[],i) = 10000000
            | findHelper(v,a::l,i) = if a = v then i else findHelper(v,l,i+1)
    in
        findHelper(v,lst,0)
    end
    
    
  
  val precolored_tmps = specialregs@argregs@callersaves@calleesaves
  val precoloredregisters = ["$v0","$fp","$sp","$ra","$0","$a0","$a1","$a2","$a3","$t0","$t1","$t2","$t3","$t4","$t5","$t6","$t7","$t8","$t9","$s0","$s1","$s2","$s3","$s4","$s5","$s6","$s7"] 
  fun perPreColored(index,map) =
    Temp.Map.insert(map,List.nth(precolored_tmps,index),List.nth(precoloredregisters,index))
  fun indexes (lst) =
    let
      fun helper (a::l,index) = index::helper(l,index+1)
        | helper ([],index) = []
    in
      helper(lst,0)
    end
  val tempMap = foldl perPreColored Temp.Map.empty (indexes precolored_tmps)

  val registers = ["$v0","$fp","$sp","$ra","$0","$a0","$a1","$a2","$a3","$s0","$s1","$s2","$s3","$s4","$s5","$s6","$s7","$t0","$t1","$t2","$t3","$t4","$t5","$t6","$t7","$t8","$t9"] 
    
  
  fun getTempFromString str = List.nth(all_regs,findIndex(str,registers))
  
  fun getStringFromTemp tmp = 
        let val ind = findIndex(tmp, all_regs)
        in
            if ind < 5 then SOME(List.nth(registers, ind)) else NONE
        end
  fun tempToString tmp = 
        let val str_opt = getStringFromTemp(tmp)
        in if isSome str_opt then valOf str_opt else Temp.makestring(tmp)
        end
  
  
  datatype frag = PROC of {body: Tree.stm, frame: frame}
                | STRING of Temp.label * string
  fun exp (acc, tExp) = case acc of
  	InFrame(k) => T.MEM(T.BINOP(T.PLUS, T.CONST(k), tExp))
  | InReg(x) => T.TEMP(x)

  (* allocates a new frame *)
	fun newFrame {name, formals} =  
    let
      fun allocate([], finishedList, regs, offset) = (finishedList, offset)
        | allocate(first::rest, currentList, regs, offset) = 
            case first of 
              true => (allocate(rest, currentList@[(InFrame offset)], regs, offset + wordSize))
            | false => 
                if 
                  regs > 4 
                then (* put in frame *)
                  allocate(rest, currentList@[(InFrame offset)], regs, offset + wordSize)
                else (* put in reg *)
                  allocate(rest, currentList@[(InReg (Temp.newtemp()))], regs + 1, offset)
      val (myFormals, myOffset) = allocate((formals), [], 0, 0)

    in
      {
        name=name,
        formals=myFormals,
        locals=ref 0,
        offset=(ref (myOffset))
      }
    end

	fun name {name=name, formals=_, locals=_, offset=_} = name

	fun formals {name=_, formals=formals, locals=_, offset=_} = (formals)

  (* determines whether goes in frame or reg based on whether it escapes *)
	fun allocLocal my_frame escapes = 
    let 
      fun increaseLocals {name=_, formals=_, locals=num, offset=_} = num := !num + 1
      fun increaseOffset {name=_, formals=_, locals=_, offset=num} = num := !num + wordSize
      fun getOffset {name=_, formals=_, locals=_, offset=num} = !num
      fun getName {name=n, formals=_, locals=_, offset=_} = n
      val retVal = InFrame(getOffset my_frame)
    in
      increaseLocals my_frame;
      case escapes of
        true => (increaseOffset my_frame; retVal)
        | false => InReg(Temp.newtemp())
    end

    fun extCall(s, args) = T.CALL(T.NAME(Temp.namedlabel(s)), args)

    (* for each incoming register parameter, move it to the place from which it is seen from within the function *)
    fun procEntryExit1 (fr, stm) = 
      let
        fun moveArguments (firstAccess::restAccess, instList, offset) = 
              (
                if 
                  offset < 4
                then
                  T.MOVE(exp(firstAccess, T.TEMP(FP)), T.TEMP(List.nth(argregs, offset)))::moveArguments(restAccess, instList, offset+1)
                else
                  (
                    case firstAccess of 
                        InFrame frameOffset => moveArguments(restAccess, instList, offset+1)
                      | InReg regTemp => T.MOVE(exp(firstAccess, T.TEMP(FP)), T.TEMP(regTemp))::moveArguments(restAccess, instList, offset+1)
                  )
              )
          | moveArguments ([], instList, offset) = instList
        val theFormals = formals(fr)
        val addedStms = moveArguments(theFormals, [], 0)
        fun makeStm ([], stm) = stm
          | makeStm (addedStuff, stm) = T.SEQ(addedStuff @ [stm])

      in
        makeStm(addedStms, stm) 
      end
    fun procEntryExit2(frame,body) = 
        body @
        [Assem.OPER{assem="",
            src=[getTempFromString("$0"),getTempFromString("$ra"),
            getTempFromString("$sp"),getTempFromString("$fp")],
            dst=[],jump=SOME[]}]

    fun smlToTiger a = if (a<0) then ("-"^Int.toString(~a)) else Int.toString(a)

    fun procEntryExit3(my_frame as {name=my_name, formals=my_formals, locals=my_locals, offset=my_offset}: frame, body, registersToSave) =

      let 
        (* generate label *)
        val func_label = name (my_frame)
        val funcLabelInsn = [Assem.LABEL {assem=Symbol.name func_label ^ ":\n", lab=func_label}]

        (*move fp into a0 for tig_main *)
        val tmp_tig_main = Assem.OPER {assem="move `d0, `s0\n", src=[getTempFromString("$fp")], dst=[getTempFromString("$a0")], jump=NONE}

        val tig_main_insn = (if (my_name = Symbol.symbol "tig_main") then [tmp_tig_main] else [])

        (* save fp to stack *)
        val storeFpToStack = [Assem.OPER {assem="sw `d0, -4(`s0)\n", src=[getTempFromString("$sp")], dst=[getTempFromString("$fp")], jump=NONE}]

        (* move sp to fp *)
        val moveSpToFp = [Assem.OPER {assem="move `d0, `s0\n", src=[getTempFromString("$sp")], dst=[getTempFromString("$fp")], jump=NONE}]

        (* calculate new sp offset *)
        val spOffset =  !my_offset + wordSize*(length(registersToSave) + 1) (* 1 for save *)
                          

        (* subtract from sp *)
        val subtractSp = [Assem.OPER {assem="addi `d0, `s0, -"^Int.toString(spOffset) ^ "\n", src=[getTempFromString("$fp")], dst=[getTempFromString("$sp")], jump=NONE}]

        (* store registers to save *)
        fun storeRegisters(firstReg::otherRegs, moved, offset) = 
              (Assem.OPER {assem="sw `s0, "^smlToTiger(offset)^"(`s1)\n", src=[firstReg, getTempFromString("$fp")], dst=[], jump=NONE})::storeRegisters(otherRegs, moved, offset-4)
          | storeRegisters([], moved, offset) = moved
        val storeRegisterInstructions = storeRegisters(registersToSave, [], ~8) (* -8 because fp is in location -4 *)

        (* moving return value into rv *)
        (* this is done in procEntryExit *)

        (* same thing as store except with loads *)
        fun loadRegisters(firstReg::otherRegs, moved, offset) = 
              (Assem.OPER {assem="lw `d0, "^smlToTiger(offset)^"(`s0)\n", src=[getTempFromString("$fp")], dst=[firstReg], jump=NONE})::loadRegisters(otherRegs, moved, offset-4)
          | loadRegisters([], moved, offset) = moved
        val loadRegisterInstructions = loadRegisters(registersToSave, [], ~8) (* -8 because fp is in location -4 *)
        
        (* move fp to sp *)
        val moveFpToSp = [Assem.OPER {assem="move `d0, `s0\n", src=[getTempFromString("$fp")], dst=[getTempFromString("$sp")], jump=NONE}]

        (* follow sl to reset fp to previous frame's fp *)
        val resetFp = [Assem.OPER {assem="lw `d0, -4(`s0)\n", src=[getTempFromString("$fp")], dst=[getTempFromString("$fp")], jump=NONE}]

        (* return insn *)
        val returnInsn = [Assem.OPER {assem="jr `d0\n", src=[], dst=[getTempFromString("$ra")], jump=NONE}]

      in
        {prolog = "PROCEDURE "^(Symbol.name (name my_frame))^"\n",
            body = 
              funcLabelInsn @ tig_main_insn @ storeFpToStack @ moveSpToFp @ subtractSp @ storeRegisterInstructions @ body @ loadRegisterInstructions @ 
              moveFpToSp @ resetFp @ returnInsn, 
            epilog = "END "^(Symbol.name (name my_frame)) ^ "\n"}
      end

end
