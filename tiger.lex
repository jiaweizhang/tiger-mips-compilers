type svalue = Tokens.svalue
type pos = int
type ('a, 'b) token = ('a, 'b) Tokens.token
type lexresult = (svalue, pos) token

val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
fun err(p1,p2) = ErrorMsg.error p1

val commentDepth = ref 0
val tempString = ref ""
val tempStringIndex = ref 0
val tempStringBoolean = ref 0

fun eof() = 
	let 
		val pos = hd(!linePos) 
	in 
		if (!commentDepth <> 0)
			then (ErrorMsg.error pos ("can't end file on comment"))
			else (
				if (!tempStringBoolean = 1)
					then (ErrorMsg.error pos ("can't end file on string"))
					else ()
			);
		Tokens.EOF(pos,pos) 
	end

	%%
	
%s COMMENT STRING;
%header (functor TigerLexFun(structure Tokens: Tiger_TOKENS));
	
	%%

<INITIAL>"type" 		=> (Tokens.TYPE  (yypos, yypos+4));   
<INITIAL>"var" 			=> (Tokens.VAR     (yypos, yypos+3));
<INITIAL>"function" 	=> (Tokens.FUNCTION     (yypos, yypos+8));
<INITIAL>"break"		=> (Tokens.BREAK     (yypos, yypos+5));
<INITIAL>"of"			=> (Tokens.OF     (yypos, yypos+2));
<INITIAL>"end" 			=> (Tokens.END     (yypos, yypos+3));
<INITIAL>"in"			=> (Tokens.IN     (yypos, yypos+2));
<INITIAL>"nil"			=> (Tokens.NIL     (yypos, yypos+3));
<INITIAL>"let"			=> (Tokens.LET     (yypos, yypos+3));
<INITIAL>"do"			=> (Tokens.DO     (yypos, yypos+2));
<INITIAL>"to"			=> (Tokens.TO     (yypos, yypos+2));
<INITIAL>"for"			=> (Tokens.FOR     (yypos, yypos+3));
<INITIAL>"while"		=> (Tokens.WHILE     (yypos, yypos+5));
<INITIAL>"else"			=> (Tokens.ELSE     (yypos, yypos+4));
<INITIAL>"then"			=> (Tokens.THEN     (yypos, yypos+4));
<INITIAL>"if"			=> (Tokens.IF     (yypos, yypos+2));
<INITIAL>"array"		=> (Tokens.ARRAY     (yypos, yypos+5));
<INITIAL>":="			=> (Tokens.ASSIGN     (yypos, yypos+2));
<INITIAL>"|"			=> (Tokens.OR     (yypos, yypos+1));
<INITIAL>"&"			=> (Tokens.AND     (yypos, yypos+1));
<INITIAL>">="			=> (Tokens.GE     (yypos, yypos+2));
<INITIAL>">"			=> (Tokens.GT     (yypos, yypos+1));
<INITIAL>"<="			=> (Tokens.LE     (yypos, yypos+2));
<INITIAL>"<"			=> (Tokens.LT     (yypos, yypos+1));
<INITIAL>"<>"			=> (Tokens.NEQ     (yypos, yypos+2));
<INITIAL>"="			=> (Tokens.EQ     (yypos, yypos+1));
<INITIAL>"/"			=> (Tokens.DIVIDE     (yypos, yypos+1));
<INITIAL>"*"			=> (Tokens.TIMES     (yypos, yypos+1));
<INITIAL>"-"			=> (Tokens.MINUS     (yypos, yypos+1));
<INITIAL>"+"			=> (Tokens.PLUS     (yypos, yypos+1));
<INITIAL>"."			=> (Tokens.DOT     (yypos, yypos+1));
<INITIAL>"}"			=> (Tokens.RBRACE     (yypos, yypos+1));
<INITIAL>"{"			=> (Tokens.LBRACE     (yypos, yypos+1));
<INITIAL>"]"			=> (Tokens.RBRACK     (yypos, yypos+1));
<INITIAL>"["			=> (Tokens.LBRACK     (yypos, yypos+1));
<INITIAL>")"			=> (Tokens.RPAREN     (yypos, yypos+1));
<INITIAL>"("			=> (Tokens.LPAREN     (yypos, yypos+1));
<INITIAL>";"			=> (Tokens.SEMICOLON     (yypos, yypos+1));
<INITIAL>":"			=> (Tokens.COLON     (yypos, yypos+1));
<INITIAL>","			=> (Tokens.COMMA     (yypos, yypos+1));

<INITIAL>[0-9]*			=> (Tokens.INT(valOf (Int.fromString yytext), yypos, yypos+size yytext));
<INITIAL>[a-zA-Z][a-zA-Z0-9_]* 	=> (Tokens.ID(yytext, yypos, yypos+size yytext));

<INITIAL>\n				=> (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());
<INITIAL>[ ]+			=> (continue());
<INITIAL>[\t]+ 			=> (continue());

<INITIAL>\"				=> (YYBEGIN STRING; tempString := "" ; tempStringIndex := yypos; tempStringBoolean := 1; continue());
<STRING>\"				=> (YYBEGIN INITIAL; tempStringIndex := yypos; tempStringBoolean := 0; Tokens.STRING (!tempString, !tempStringIndex, !tempStringIndex + (size (!tempString))));
<STRING>\\n 			=> (tempString := !tempString ^ "\n" ; continue());
<STRING>\\t 			=> (tempString := !tempString ^ "\t" ; continue());
<STRING>\\[\^][@-Z] 	=> (tempString := !tempString ^ (String.str (Char.chr (Char.ord (valOf (Char.fromString (String.substring(yytext,2,1))))  - 64))); continue());
<STRING>\\[0-9][0-9][0-9] => (let val ascii = valOf (Int.fromString (String.substring(yytext,1,3))) in if ascii <= 255 then tempString := (!tempString ^ (Char.toString(chr ascii))) else (ErrorMsg.error yypos ("illegal ascii code: "^yytext)) end; continue());
<STRING>\\\"			=> (tempString := !tempString ^ "\"" ; continue());
<STRING>\\\\			=> (tempString := !tempString ^ "\\" ; continue());
<STRING>\\[ \t\n\f]+\\	=> (continue());
<STRING>\n				=> (ErrorMsg.error yypos ("can't have newline in a string"); continue());
<STRING>[ -!#-\[\]-~]+	=> (tempString := !tempString ^ yytext; continue());
<STRING>.				=> (ErrorMsg.error yypos ("illegal character in string: " ^ yytext); continue());

<INITIAL>"/*"			=> (YYBEGIN COMMENT; commentDepth := !commentDepth + 1; continue());
<INITIAL>"*/"			=> (ErrorMsg.error yypos ("illegal endcomment symbol without a begincomment symbol"); continue());
<COMMENT>"/*"			=> (commentDepth := !commentDepth + 1; continue());
<COMMENT>"*/"			=> (commentDepth := !commentDepth - 1; if (!commentDepth = 0) then (YYBEGIN INITIAL; continue()) else continue());
<COMMENT>\n				=> (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());
<COMMENT>[ ]+			=> (continue());
<COMMENT>[\t]+ 			=> (continue());
<COMMENT>.				=> (continue());

<INITIAL>.				=> (ErrorMsg.error yypos ("illegal character: " ^ yytext); continue());
