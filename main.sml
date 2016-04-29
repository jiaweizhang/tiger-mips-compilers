structure Main = struct

    fun getMaxArgs(fragmentList) =
      let
        fun numFormals fragment= 
          case fragment of
              F.STRING(_,_) => 0
            | F.PROC {body, frame} => length(F.formals frame)
        fun helper(fragment, currentMax) =
          case fragment of
              F.STRING(_,_) => 0
            | F.PROC {body=my_body, frame=my_frame} => if 
                                                          currentMax < length(F.formals (my_frame))
                                                        then
                                                          numFormals (fragment)
                                                        else
                                                          currentMax
      in
        foldl helper 0 fragmentList
      end

    fun tempToAllocated allocation tmp = 
        let
            val reg = valOf (Temp.Map.find(allocation,tmp)) 
        in
            reg
        end

    fun addEscape(index) = 
      let 
        val escapes = FindEscape.getEscapes ()
      in
        if 
          !(List.nth(!escapes, index)) = false
        then 
          (List.nth(!escapes, index) := true)
        else 
          addEscape(index + 1)
      end

    fun printRuntime(outstream) =
      let
        val stream = TextIO.openIn "runtimele.s"
        val _ = TextIO.output(outstream, TextIO.inputAll stream)
      in
        ()
      end

    fun printSysspim(outstream) =
      let
        val stream = TextIO.openIn "sysspim.s"
        val _ = TextIO.output(outstream, TextIO.inputAll stream)
      in
        ()
      end

    fun printFinalAssembly (instructionList, outstream) = 
      let
        val concatedInstructions = String.concat(instructionList)
        val _ = TextIO.output(outstream, concatedInstructions)
      in
        ()
      end

    fun createInstrs (F.PROC{body,frame}, (inputSpill, outstream, logstream)) =
        let
            val lin = Canon.linearize body
            val blocks = Canon.basicBlocks lin
            val stms = Canon.traceSchedule blocks
            
            val _ = TextIO.output(logstream, "\n\n\nCanonized IR:\n================\n\n")
            val _ = map (Printtree.printtree (logstream)) stms

            val instrs = List.concat(map (MipsGen.codegen frame) stms) 

            val _ = TextIO.output(logstream, "\n\n\nOriginal Instructions:\n=====================\n\n")
            val _ = TextIO.output(logstream, String.concat(map (Assem.format(F.tempToString)) instrs))

            val instrsAfterProc2 = F.procEntryExit2(frame, instrs)

            val (instrs', alloc, isSpilled) = Reg_Alloc.alloc(instrsAfterProc2) 

            val registersToSave = F.getTempFromString("$ra")::F.calleesaves 

            val finalInstructions = #body(F.procEntryExit3(frame, instrs', registersToSave))
            val _ = if 
                      isSpilled 
                    then 
                      () 
                    else 
                      printFinalAssembly(map (Assem.format(tempToAllocated alloc)) finalInstructions, outstream)

            val _ = TextIO.output(outstream, "\n\n\n")

            val _ = TextIO.output(logstream, "\n\n\nFinal Instructions:\n=====================\n\n")
            val _ = TextIO.output(logstream, String.concat(map (Assem.format(tempToAllocated alloc)) finalInstructions))

            val outSpill = if (isSpilled) then true else inputSpill

        in
            (outSpill, outstream, logstream)
        end
    | createInstrs (F.STRING(lab,s), (inputSpill, outstream, logstream)) = (inputSpill, outstream, logstream)

    fun compileHelper (absyn, filename) = 
      let
            (* open file for printing *)
            val _ = TextIO.openOut(filename^".s")
            val outstream = TextIO.openAppend(filename^".s")

            (* open log file for debug *)
            val _ = TextIO.openOut("log.txt")
            val logstream = TextIO.openAppend("log.txt")

            val frags = Semant.transProg absyn

            val _ = TextIO.output(outstream, "\n.data\n")
            fun printStrings (F.PROC{body, frame}) = ()
              | printStrings (F.STRING(lab, s)) = (TextIO.output(outstream, F.toString(lab, s)))
            val _ = map (printStrings) frags
            val _ = TextIO.output(outstream, "\n.text\n")
            val _ = printRuntime (outstream)
            
            val _ = TextIO.output(outstream, "\n\n\n\n\n\n# begin of final assembly\n\n")

            val isSpilled = foldl createInstrs (false, outstream, logstream) frags

            val _ = TextIO.output(outstream, "\n\n\n\n\n\n# begin of sysspim\n\n")
            val _ = printSysspim (outstream)
      in
        (* recursively call itself and print again if spilled *)
        if (# 1 (isSpilled)) then (addEscape(0) ;compileHelper (absyn, filename)) else ()
      end

    fun compile filename = 
        let
            val _ = Translate.emptyFragList ()
            val absyn = Parse.parse filename
            val _ = FindEscape.resetEscapes ()
            val _ = FindEscape.findEscape absyn
        in
            compileHelper (absyn, filename)
        end

end