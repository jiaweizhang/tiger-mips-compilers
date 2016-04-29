signature REG_ALLOC = 
sig
    type allocation = MipsFrame.register Temp.Map.map
    val alloc : Assem.instr list -> Assem.instr list * allocation * bool
end
structure Reg_Alloc : REG_ALLOC =
struct
    type allocation = MipsFrame.register Temp.Map.map
    
    fun alloc (instrs) = 
        let
            fun printflowgraph (fg:Flow.flowgraph) =
                let 
                    val graph = case fg of Flow.FLOWGRAPH{control=c,...} => c
                in
                    G.printGraph (fn (nodeid,instr) => ("(Node-"^(Int.toString nodeid)^"): "^(Assem.format(F.tempToString) instr))) graph
                end
            val (flowgraph,nodelist) = MakeGraph.instrs2graph instrs
            val (igraphdatatype,liveOutMap) = Liveness.interferenceGraph flowgraph        
            val (graph,tnode,gtemp,moves) = case igraphdatatype of Liveness.IGRAPH{graph=gr,tnode=tn,gtemp=gt,moves=m} => (gr,tn,gt,m)
            val (allocation,spills) = Color.color {interference=igraphdatatype,initial=MipsFrame.tempMap, spillCost= (fn x => 1), registers=MipsFrame.registers}
        in
            if List.length spills = 0 then (instrs,allocation, false) else (instrs, allocation, true)
        end

end