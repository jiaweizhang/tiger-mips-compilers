structure Types =
struct

  	type unique = unit ref

  	datatype ty = 
		RECORD of (Symbol.symbol * ty) list * unique
		| NIL
		| INT
		| STRING
		| ARRAY of ty * unique
		| NAME of Symbol.symbol * ty option ref
		| UNIT
		| BOTTOM

  	datatype sets = 
		SUB
		| SUP
		| SAM
		| BAD

  	fun subSam(BOTTOM, _) = true
		| subSam(_, UNIT) = true
		| subSam(NIL, RECORD(_)) = true
		| subSam(NIL, NIL) = true
		| subSam(INT, INT) = true
		| subSam(STRING, STRING) = true
		| subSam(RECORD(_, uniqA), RECORD(_, uniqB)) = uniqA = uniqB
		| subSam(ARRAY(_, uniqA), ARRAY(_, uniqB)) = uniqA = uniqB
		| subSam(NAME(symA, _), NAME(symB, _)) = String.compare(Symbol.name symA, Symbol.name symB) = EQUAL
		| subSam(_, _) = false

    fun check(a, b) = 
    	if subSam(a, b) andalso subSam(b, a)
    		then SAM
    	else if subSam(a, b)
    		then SUB
    	else if subSam(b, a)
    		then SUP
    	else
    		BAD
    fun toString(RECORD(lst,un)) = "Record("^(String.concatWith ","(map toString (map #2 lst)))^")"
		| toString(NIL) = "Nil"
		| toString(INT) = "Int"
		| toString(STRING) = "String"
		| toString(ARRAY(t,un)) = "Array("^(toString t)^")"
		| toString(NAME(sym,un)) = "Name("^(Symbol.name sym)^")"
		| toString(UNIT) = "Unit"
		| toString(BOTTOM) = "Bottom"
end

