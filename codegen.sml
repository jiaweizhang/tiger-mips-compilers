signature CODEGEN = 
sig
    structure Frame : FRAME
    val codegen : Frame.frame -> Tree.stm -> Assem.instr list
end

structure MipsGen : CODEGEN = 
struct
structure Frame = MipsFrame
structure A = Assem
structure T = Tree
fun relop_toString(T.EQ) = "eq"
  | relop_toString(T.NE) = "ne"
  | relop_toString(T.LT) = "lt"
  | relop_toString(T.GT) = "gt"
  | relop_toString(T.LE) = "le"
  | relop_toString(T.GE) = "ge"
  | relop_toString(T.ULT) = "ltu"
  | relop_toString(T.ULE) = "leu"
  | relop_toString(T.UGT) = "gtu"
  | relop_toString(T.UGE) = "gte"

fun getString(i) = if (i>=0) then Int.toString(i) else ("-"^Int.toString(~i))

fun symstr sym = Symbol.name sym

fun codegen (frame) (stm: Tree.stm) : Assem.instr list =
  let
      val ilist = ref (nil: Assem.instr list)
      fun emit x = ilist := x :: !ilist

      fun munchStm (T.EXP(e1)) = (munchExp e1; ())
        | munchStm (T.SEQ(lst)) = hd (rev (map munchStm lst))

        (* MEM Store Optimizations *)
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, e1, T.CONST i)),e2)) = 
          emit(A.OPER{assem="sw `s0, " ^ getString i ^ "(`s1)\n",
                      src=[munchExp e2, munchExp e1],dst=[],jump=NONE}
              )
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.CONST i, e1)),e2)) = 
          emit(A.OPER{assem="sw `s0, " ^ getString i ^ "(`s1)\n",
                      src=[munchExp e2, munchExp e1],dst=[],jump=NONE}
              )
        | munchStm(T.MOVE(T.MEM(T.BINOP(T.MINUS, e1, T.CONST i)),e2)) = 
          emit(A.OPER{assem="sw `s0, " ^ getString (~i) ^ "(`s1)\n",
                      src=[munchExp e2, munchExp e1],dst=[],jump=NONE}
              )
        | munchStm(T.MOVE(T.MEM(e1),e2)) = 
          emit(A.OPER{assem="sw `s0, 0(`s1)\n",
                      src=[munchExp e2, munchExp e1],dst=[],jump=NONE}
              )

        (* MEM to Temp Optimizations *)
        | munchStm(T.MOVE(T.TEMP(t1), T.MEM(T.BINOP(T.PLUS, e1, T.CONST i)))) = 
          emit(A.OPER{assem="lw `d0, " ^ getString i ^ "(`s0)\n",
                      src=[munchExp e1],dst=[t1],jump=NONE}
              )
        | munchStm(T.MOVE(T.TEMP(t1), T.MEM(T.BINOP(T.PLUS, T.CONST i, e1)))) = 
          emit(A.OPER{assem="lw `d0, " ^ getString i ^ "(`s0)\n",
                      src=[munchExp e1],dst=[t1],jump=NONE}
              )
        | munchStm(T.MOVE(T.TEMP(t1), T.MEM(T.BINOP(T.MINUS, e1, T.CONST i)))) = 
          emit(A.OPER{assem="lw `d0, " ^ getString (~i) ^ "(`s0)\n",
                      src=[munchExp e1],dst=[t1],jump=NONE}
              )

        (* load immediates and addresses *)
        | munchStm(T.MOVE(T.TEMP(t1), T.CONST i)) = 
          emit(A.OPER{assem="li `d0, " ^ getString (i) ^ "\n",
                      src=[],dst=[t1],jump=NONE}
              )
        | munchStm(T.MOVE(T.TEMP(t1), T.NAME(label))) = 
          emit(A.OPER{assem="la `d0, " ^ Symbol.name label ^ "\n",
                      src=[],dst=[t1],jump=NONE}
              )

        (* other moves *)
        | munchStm(T.MOVE(T.TEMP(t1), e1)) = 
          emit(A.MOVE{assem="move `d0, `s0\n",
                      src=(munchExp e1), dst=t1}
              )

        (* eseq moves *)
        | munchStm(T.MOVE(T.ESEQ(s1, T.MEM(e1)), e2)) =
          (munchStm (s1); 
           emit(A.OPER{assem="sw `s0, 0(`d0)\n",
                       src=[munchExp e2], dst=[munchExp e1],jump=NONE}
               )
          )
        | munchStm(T.MOVE(T.ESEQ(s1, T.TEMP(t1)), e1)) =
          (munchStm (s1); 
           emit(A.OPER{assem="move `d0, `s0\n",
                       src=[munchExp e1], dst=[t1],jump=NONE}
               )
          )
        | munchStm(T.MOVE(T.ESEQ(s1, T.ESEQ(some)), e1)) =
          (munchStm (s1); munchStm(T.MOVE(T.ESEQ(some), e1)))

        (* should never happen *)


        | munchStm(T.JUMP(T.NAME(label),lst)) = 
          emit(A.OPER{assem="j " ^ Symbol.name label ^ "\n",
                      src=[],dst=[],jump=SOME(lst)}
              )
        | munchStm(T.JUMP(e1,lst)) = 
          emit(A.OPER{assem="jr `j0\n",
                      src=[munchExp e1],dst=[],jump=SOME(lst)}
              )
        | munchStm(T.CJUMP(relop,e1,e2,lt,lf)) = 
          emit(A.OPER{assem="b"^(relop_toString relop)^" `s0,`s1, "^(symstr lt)^"\n", 
                      src=[munchExp e1, munchExp e2],dst=[],jump=SOME [lt,lf]}
              )
        | munchStm(T.LABEL(lab)) = 
          emit(A.LABEL{assem=symstr lab ^":\n",
                       lab=lab}
              )               

      and result(gen) = let val t = Temp.newtemp() in gen t; t end

      (* BINOP *)
      (* Optimized immediates *)
      and munchExp(T.BINOP(T.PLUS, e1, T.CONST i)) = 
          result(fn r => emit(
                            A.OPER {assem="addi `d0, `s0, " ^ getString i ^ "\n",
				    src=[munchExp e1],dst=[r],jump=NONE}
                        )
                )
        | munchExp(T.BINOP(T.PLUS, T.CONST i, e1)) = 
          result(fn r => emit(
                            A.OPER {assem="addi `d0, `s0, " ^ getString i ^ "\n",
				    src=[munchExp e1],dst=[r],jump=NONE}
                        )
                )
        | munchExp(T.BINOP(T.MINUS, e1, T.CONST i)) = 
          result(fn r => emit(
                            A.OPER {assem="addi `d0, `s0, " ^ getString (~i) ^ "\n",
				    src=[munchExp e1],dst=[r],jump=NONE}
                        )
                )
        | munchExp(T.BINOP(T.AND, e1, T.CONST i)) = 
          result(fn r => emit(
                            A.OPER {assem="andi `d0, `s0, " ^ getString i ^ "\n",
				    src=[munchExp e1],dst=[r],jump=NONE}
                        )
                )
        | munchExp(T.BINOP(T.AND, T.CONST i, e1)) = 
          result(fn r => emit(
                            A.OPER {assem="andi `d0, `s0, " ^ getString i ^ "\n",
				    src=[munchExp e1],dst=[r],jump=NONE}
                        )
                )
        | munchExp(T.BINOP(T.OR, e1, T.CONST i)) = 
          result(fn r => emit(
                            A.OPER {assem="ori `d0, `s0, " ^ getString i ^ "\n",
				    src=[munchExp e1],dst=[r],jump=NONE}
                        )
                )
        | munchExp(T.BINOP(T.OR, T.CONST i, e1)) = 
          result(fn r => emit(
                            A.OPER {assem="ori `d0, `s0, " ^ getString i ^ "\n",
				    src=[munchExp e1],dst=[r],jump=NONE}
                        )
                )
        | munchExp(T.BINOP(T.XOR, e1, T.CONST i)) = 
          result(fn r => emit(
                            A.OPER {assem="xori `d0, `s0, " ^ getString i ^ "\n",
				    src=[munchExp e1],dst=[r],jump=NONE}
                        )
                )
        | munchExp(T.BINOP(T.XOR, T.CONST i, e1)) = 
          result(fn r => emit(
                            A.OPER {assem="xori `d0, `s0, " ^ getString i ^ "\n",
				    src=[munchExp e1],dst=[r],jump=NONE}
                        )
                )

        (* Regular alu operations *)
        | munchExp(T.BINOP(T.PLUS, e1, e2)) = 
          result(fn r => emit(
                            A.OPER {assem="add `d0, `s0, `s1\n",
				    src=[munchExp e1, munchExp e2],dst=[r],jump=NONE}
                        )
                )
        | munchExp(T.BINOP(T.MINUS, e1, e2)) = 
          result(fn r => emit(
                            A.OPER {assem="sub `d0, `s0, `s1\n",
				    src=[munchExp e1, munchExp e2],dst=[r],jump=NONE}
                        )
                )
        | munchExp(T.BINOP(T.MUL, e1, e2)) = 
          result(fn r => emit(
                            A.OPER {assem="mul `d0, `s0, `s1\n",
				    src=[munchExp e1, munchExp e2],dst=[r],jump=NONE}
                        )
                )


        | munchExp(T.BINOP(T.DIV, e1, e2)) = 
          result(fn r => emit(
                            A.OPER {assem="div `d0, `s0, `s1\n",
				    src=[munchExp e1, munchExp e2],dst=[r],jump=NONE}
                        )
                )
        | munchExp(T.BINOP(T.AND, e1, e2)) = 
          result(fn r => emit(
                            A.OPER {assem="and `d0, `s0, `s1\n",
				    src=[munchExp e1, munchExp e2],dst=[r],jump=NONE}
                        )
                )
        | munchExp(T.BINOP(T.OR, e1, e2)) = 
          result(fn r => emit(
                            A.OPER {assem="or `d0, `s0, `s1\n",
				    src=[munchExp e1, munchExp e2],dst=[r],jump=NONE}
                        )
                )
        | munchExp(T.BINOP(T.XOR, e1, e2)) = 
          result(fn r => emit(
                            A.OPER {assem="xor `d0, `s0, `s1\n",
				    src=[munchExp e1, munchExp e2],dst=[r],jump=NONE}
                        )
                )

        (* Shift operations constant *)
        | munchExp(T.BINOP(T.LSHIFT, e1, T.CONST i)) = 
          result(fn r => emit(
                            A.OPER {assem="sll `d0, `s0, " ^ getString i ^ "\n",
				    src=[munchExp e1],dst=[r],jump=NONE}
                        )
                )
        | munchExp(T.BINOP(T.RSHIFT, e1, T.CONST i)) = 
          result(fn r => emit(
                            A.OPER {assem="srl `d0, `s0, " ^ getString i ^ "\n",
				    src=[munchExp e1],dst=[r],jump=NONE}
                        )
                )
        | munchExp(T.BINOP(T.ARSHIFT, e1, T.CONST i)) = 
          result(fn r => emit(
                            A.OPER {assem="sra `d0, `s0, " ^ getString i ^ "\n",
				    src=[munchExp e1],dst=[r],jump=NONE}
                        )
                )

        (* Shift operations variable *)
        | munchExp(T.BINOP(T.LSHIFT, e1, e2)) = 
          result(fn r => emit(
                            A.OPER {assem="sllv `d0, `s0, `s1\n",
				    src=[munchExp e1, munchExp e2],dst=[r],jump=NONE}
                        )
                )
        | munchExp(T.BINOP(T.RSHIFT, e1, e2)) = 
          result(fn r => emit(
                            A.OPER {assem="srlv `d0, `s0, `s1\n",
				    src=[munchExp e1, munchExp e2],dst=[r],jump=NONE}
                        )
                )
        | munchExp(T.BINOP(T.ARSHIFT, e1, e2)) = 
          result(fn r => emit(
                            A.OPER {assem="srav `d0, `s0, `s1\n",
				    src=[munchExp e1, munchExp e2],dst=[r],jump=NONE}
                        )
                )

        (* MEM *)
        (* optimized load operations *)
        | munchExp(T.MEM(T.BINOP(T.PLUS, e1, T.CONST i))) =
          result(fn r => emit (
                            A.OPER {assem="lw `d0, " ^ getString i ^ "(`s0)" ^ "\n",
				    src=[munchExp e1], dst=[r], jump=NONE}
                        )
                )
        | munchExp(T.MEM(T.BINOP(T.PLUS, T.CONST i, e1))) =
          result(fn r => emit (
                            A.OPER {assem="lw `d0, " ^ getString i ^ "(`s0)" ^ "\n",
				    src=[munchExp e1], dst=[r], jump=NONE}
                        )
                )
        | munchExp(T.MEM(T.BINOP(T.MINUS, e1, T.CONST i))) =
          result(fn r => emit (
                            A.OPER {assem="lw `d0, " ^ getString (~i) ^ "(`s0)" ^ "\n",
				    src=[munchExp e1], dst=[r], jump=NONE}
                        )
                )
        | munchExp(T.MEM(e1)) = 
          result(fn r => emit(
                            A.OPER {assem="lw `d0, 0(`s0)\n",
				    src=[munchExp e1],dst=[r],jump=NONE}
                        )
                )

        (* TEMP *)
        | munchExp(T.TEMP(t)) = t
        | munchExp(T.ESEQ(stm,e1)) = (munchStm stm; munchExp e1)
        | munchExp(T.NAME(lab)) = result(fn r => emit(A.OPER
							  {assem="la `d0, " ^symstr lab^"\n",
							   src=[],dst=[r],jump=NONE}))  
        | munchExp(T.CONST(0)) = MipsFrame.getTempFromString("$0")      
        | munchExp(T.CONST(i)) = result(fn r => emit(A.OPER
							 {assem="li `d0, "^(Int.toString i)^"\n",
							  src=[],dst=[r],jump=NONE}))
        | munchExp(T.CALL(T.NAME lab,args)) = 
          let
              val calldefs = MipsFrame.newcallersaves
          (* val _ = map (fn x => print(Int.toString x)) calldefs *)
          in
              (emit(A.OPER{assem="jal "^(symstr lab)^" \n",
                           src=munchArgs(0,args, 8),dst=calldefs,jump=NONE});
               MipsFrame.getTempFromString("$v0"))
          end        


      and munchArgs(i,arg::args, currentOffset) = 
          let
              val moveLeftTemp = if i < 4
				 then List.nth(MipsFrame.argregs, i)
				 else Temp.newtemp()
              fun moveToTemp arg = munchStm(T.MOVE(T.TEMP(moveLeftTemp), arg))
              fun moveToFrame (arg, offset) = munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP(MipsFrame.getTempFromString("$sp")), T.CONST offset)), arg))
          in
              if 
                  (i < 4)
              then
                  (moveToTemp (arg); moveLeftTemp::munchArgs(i+1, args, currentOffset))
              else
                  (moveToFrame (arg, currentOffset); munchArgs(i+1, args, currentOffset+4)) 
          end
        | munchArgs(i,[], currentOffset) = []
  in
      (munchStm stm;rev(!ilist))
  end
end
