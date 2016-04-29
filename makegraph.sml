
structure G = FuncGraph(IntKey)
structure Flow =
struct
    structure FGraph = G
    structure NodeMap = SplayMapFn(IntKey)
    
    datatype flowgraph = 
        FLOWGRAPH of {control: Assem.instr FGraph.graph,
                      def: Temp.temp list NodeMap.map,
                      use: Temp.temp list NodeMap.map,
                      ismove: bool NodeMap.map}
                      
    fun makeUse(g) = 
        let
            val nodeList = FGraph.nodes(g)
          
            fun addUse(n, m) = 
            let
                val inst = FGraph.nodeInfo(n)
                val res = case inst of 
                    Assem.MOVE{assem=_, src=s, dst=d} => [s]
                |   Assem.OPER{assem=_, src=s, dst=d, jump = _} => s
                | Assem.LABEL(_) => []
            in
                NodeMap.insert(m, FGraph.getNodeID(n), res)
            end
        in
            foldl addUse NodeMap.empty nodeList
        end
        
    fun makeDef(g) = 
        let
            val nodeList = FGraph.nodes(g)
            
            fun addUse(n, m) = 
            let
                val inst = FGraph.nodeInfo(n)
                val res = case inst of 
                    Assem.MOVE{assem=_, src=s, dst=d} => [d]
                |   Assem.OPER{assem=_, src=s, dst=d, jump = _} => d
                | Assem.LABEL(_) => []
            in
                NodeMap.insert(m, FGraph.getNodeID(n), res)
            end
        in
            foldl addUse NodeMap.empty nodeList
        end
    
    fun makeIsMove(g) =
        let
            val nodeList = FGraph.nodes(g)
                
            
            fun thisInst(n, m) = 
                let
                    val move = case FGraph.nodeInfo(n) of
                        Assem.MOVE{assem=s, dst=_, src=_} => true
                      | _ => false
                in
                    NodeMap.insert(m, FGraph.getNodeID(n),move)
            end
        in
            foldl thisInst NodeMap.empty nodeList
        end
    
end

structure MakeGraph =
struct
  structure A = Assem;
  structure G = G
  
  val instrList:(A.instr * unit ref * G.nodeID) list ref = ref []
  
  
  val nodeNum = ref 0
  (* Body *)
  
  (* Creates nodes from a list of assembly instructions *)
  fun createNodes (assemList) = 
    let
      fun newNode((inst:A.instr, unique), graph) = 
        let 
          val _ = nodeNum := !nodeNum + 1
          val (g, n) = G.addNode'(graph, !nodeNum, inst)
          val id = G.getNodeID(n)
        in
          instrList := (inst, unique, id)::(!instrList);g
        end
    in
      foldr newNode G.empty assemList
    end


  fun createEdges (assemList: (Assem.instr * unit ref) list, nodes: Assem.instr G.graph) = 
    let

      fun pList (a::l) = (Symbol.name a)^pList(l)
        | pList ([]) = ""

      fun getID(u, (a,check, ret)::l) = if u = check then ret else getID(u, l)
      fun findLabelInstr(lb) = 
        let
            
          
          fun thisOne((a:A.instr, u),b) = case a of 
            A.LABEL{assem=s, lab=l} => if (lb = l) then (getID(u, !instrList)) else b
          | _ => b
        in
          foldl thisOne (getID(#2 (List.hd assemList), !instrList)) assemList
        end

      fun newEdge((inst, u), (last, graph)) = 
        let
          val currId = getID(u, !instrList)
          val lastId = if isSome last then (case valOf last of (li, u2) => getID(u2, !instrList)) else currId
        in
          if not (isSome last)
          then (SOME(inst, u), graph)
          else (
            case valOf last of (*Each time we make edges from the previous instruction to (the current instruction or previous's jumps)*)
            (A.OPER{assem=s, dst=_, src=_, jump=j}, _) => 
              if isSome j
                then 
                  let 
                    fun eachLab(lab, jumpgr) = G.addEdge(jumpgr, {from=lastId, to=findLabelInstr(lab)})
                  in
                    (SOME(inst,u), foldl eachLab graph (valOf j))
                  end
                else
                  (SOME(inst, u), G.addEdge(graph, {from=lastId, to=currId})))

          | (A.LABEL{assem=s, lab=_}, _) => (SOME(inst, u), G.addEdge(graph, {from=lastId, to=currId}))
          | (A.MOVE{assem=s, dst=_, src=_}, _) => (SOME(inst, u), G.addEdge(graph, {from=lastId, to=currId}))
          )
        end
    in
      #2 (foldr newEdge (NONE, nodes) assemList)
    end

  (* Makes the flow graph from assembly instructions *)
  fun instrs2graph (assemList) = 
    let 
      fun addUnit(a,b) = (a,ref ())::b
      val assemUnit = foldl addUnit [] assemList
      val nodes = createNodes (assemUnit)
      val graph = createEdges (assemUnit, nodes)
      val flowGraph = Flow.FLOWGRAPH{control=graph, def=Flow.makeDef(graph), use=Flow.makeUse(graph), ismove=Flow.makeIsMove(graph)}
    in
      (flowGraph, G.nodes(graph))
    end
end