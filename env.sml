signature ENV =
sig
    type access
    datatype enventry = VarEntry of {access: Translate.access, ty: Types.ty, assignable: bool}
                      | FunEntry of {level: Translate.level, label: Temp.label, formals: Types.ty list, result: Types.ty}
    val base_tenv : Types.ty Symbol.table
    val base_venv : enventry Symbol.table
end

structure Env : ENV =
struct
type access = unit
datatype enventry = VarEntry of {access: Translate.access, ty: Types.ty, assignable: bool}
                  | FunEntry of {level: Translate.level, label: Temp.label, formals: Types.ty list, result: Types.ty}

val base_tenv = Symbol.enter(
        Symbol.enter(Symbol.empty, Symbol.symbol("int"), Types.INT),
        Symbol.symbol("string"), Types.STRING)

val base_venv = 
    let 
        fun add ((name, ty), table) = Symbol.enter(table, Symbol.symbol name, ty)
        val funcs = [("print", FunEntry({level=Translate.outermost, label = Temp.namedlabel "tig_print", formals=[Types.STRING], result=Types.UNIT})),
                     ("flush", FunEntry({level=Translate.outermost, label=Temp.namedlabel "tig_flush", formals=[], result=Types.UNIT})),
                     ("getchar", FunEntry({level=Translate.outermost, label=Temp.namedlabel "tig_getchar", formals=[], result=Types.STRING})),
                     ("ord", FunEntry({level=Translate.outermost, label=Temp.namedlabel "tig_ord", formals=[Types.STRING], result=Types.INT})),
                     ("chr", FunEntry({level=Translate.outermost, label=Temp.namedlabel "tig_chr", formals=[Types.INT], result=Types.STRING})),
                     ("size", FunEntry({level=Translate.outermost, label=Temp.namedlabel "tig_size", formals=[Types.STRING], result=Types.INT})),
                     ("substring", FunEntry({level=Translate.outermost, label=Temp.namedlabel "tig_substring", formals=[Types.STRING, Types.INT, Types.INT], result=Types.STRING})),
                     ("concat", FunEntry({level=Translate.outermost, label=Temp.namedlabel "tig_concat", formals=[Types.STRING, Types.STRING], result=Types.STRING})),
                     ("not", FunEntry({level=Translate.outermost, label=Temp.namedlabel "tig_not", formals=[Types.INT], result=Types.INT})),
                     ("exit", FunEntry({level=Translate.outermost, label=Temp.namedlabel "tig_exit", formals=[Types.INT], result=Types.UNIT}))]
    in
        foldl add Symbol.empty funcs
    end
end
