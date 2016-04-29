signature FRAME = 
sig 
	type frame
	type access
    type register = string
	val exp : access * Tree.exp -> Tree.exp
  val tempMap : register Temp.Map.map
  val registers : register list
  val FP : Temp.temp
  val RV : Temp.temp
  val newcallersaves : Temp.temp list
  val wordSize : int
  val specialregs : Temp.temp list
  val argregs : Temp.temp list
  val calleesaves : Temp.temp list
  val callersaves : Temp.temp list
  val getTempFromString : string -> Temp.temp
  val getStringFromTemp : Temp.temp -> string option
  val tempToString  : Temp.temp -> string
  
  datatype frag = PROC of {body: Tree.stm, frame: frame}
                | STRING of Temp.label * string

	val newFrame : {name: Temp.label, 
						formals: bool list} -> frame
	val name : frame -> Temp.label
	val formals : frame -> access list
	val allocLocal : frame -> bool -> access

	val extCall : string * Tree.exp list -> Tree.exp

  val procEntryExit1 : frame * Tree.stm -> Tree.stm
  val procEntryExit2 : frame * Assem.instr list -> Assem.instr list
  val procEntryExit3 : frame * Assem.instr list * Temp.temp list -> {prolog: string, body: Assem.instr list, epilog: string}
  
  val toString : Temp.label * string -> string
end