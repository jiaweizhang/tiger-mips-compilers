

structure Liveness:
sig
    datatype igraph = 
        IGRAPH of {graph: Temp.temp G.graph,
                   tnode: Temp.temp -> Temp.temp G.node,
                   gtemp: Temp.temp G.node -> Temp.temp,
                   moves: (Temp.temp G.node * Temp.temp G.node) list}
    val interferenceGraph :
        Flow.flowgraph -> igraph * (Temp.temp G.node -> Temp.temp list)
    val show : TextIO.outstream * igraph -> unit
end
= 
struct

structure LS = SplaySetFn(IntKey)
    fun printNode(id, node) = (Int.toString id)
    fun printlst elementtostring lst = (map print (map elementtostring lst))
    fun nodeToString(node : Assem.instr G.node) = 
        let 
            val id = G.getNodeID(node) 
            val inst = G.nodeInfo(node) 
        in 
            ("Node"^(Int.toString id)^": "^(Assem.format(F.tempToString) inst))
        end
    fun stringlisttostring (a::l) = a^" "^(stringlisttostring(l))
        | stringlisttostring [] = ""
    fun mapitemToString(intkey, tempset)  = "Map Item #"^(Int.toString intkey)^": "^(stringlisttostring(map (Int.toString) (LS.listItems tempset)))^"\n"
    datatype igraph = 
        IGRAPH of {graph: Temp.temp G.graph,
                   tnode: Temp.temp -> Temp.temp G.node,
                   gtemp: Temp.temp G.node -> Temp.temp,
                   moves: (Temp.temp G.node * Temp.temp G.node) list}

    fun difference x y = 
                let 
                    fun ncontains (a::l) n = if n = a then false else ncontains l n
                    | ncontains [] n = true
                in
                    List.filter (ncontains y) x
                end
    
    fun interferenceGraph(g as Flow.FLOWGRAPH{control=c, def=d, use=u, ismove=m}) = 
        let
            val (rIn, rOut) = doLive(g, Flow.NodeMap.empty, Flow.NodeMap.empty)
            val (nodesOnlyGraph, tempToNode) = makeInterferenceNodes(c)
            fun tnode x = valOf (Flow.NodeMap.find(tempToNode, x))
            fun gtemp x = G.nodeInfo(x)
            val moves = getMoves(tnode, m, c)
            fun liveOutFunc x = LS.listItems (valOf (Flow.NodeMap.find(rOut, G.getNodeID(x))))
            val iGraph = makeEdges(rOut, c, nodesOnlyGraph)
        in
            (IGRAPH{graph=iGraph, tnode=tnode, gtemp=gtemp, moves=moves}, liveOutFunc)
        end
    
    and makeInterferenceNodes(graph) = 
        let 
            val nodeList = G.nodes(graph)
            fun addNodeTemps(n, (g,m)) = 
                let
                    val info = G.nodeInfo(n)
                    val temps = case info of
                        Assem.OPER{assem=_, src=s, dst=d, jump=_} => d@s
                      | Assem.MOVE{assem=_, src=s, dst=d} => [d]@[s]
                      | _ => []
                    fun allTemps(a:Temp.temp, (tempg, tempm)) = 
                    let
                        val (newg, newn) = G.addNode'(tempg, a, a)
                        val newm = Flow.NodeMap.insert(tempm, a, newn)
                    in
                        (newg, newm)
                    end
                in
                    foldl allTemps (g,m) temps
                end
        in
            foldl addNodeTemps (G.empty, Flow.NodeMap.empty) nodeList
        end
    
    and doLive(g as Flow.FLOWGRAPH{control=c, def=d, use=u, ismove=m}, liveIn, liveOut) = 
        let 
            val change = ref false
            val nodeList = G.nodes(c)
            fun lives(n, (lIn, lOut)) = 
                let

                      
                    val id = G.getNodeID(n)
                    val succs = G.succs(n)
                    
                    fun addEmptySet dir x = case Flow.NodeMap.find(dir, x) of
                        SOME(res) => dir
                    |   NONE => Flow.NodeMap.insert(dir, id, LS.empty)

                    fun getInOut dir x = case Flow.NodeMap.find(dir, x) of
                        SOME(res) => res
                      | NONE => LS.empty                
                    

                    val nLIn = addEmptySet lIn id
                    val nLOut = addEmptySet lOut id

                    fun perSet(aSet, bSet) = LS.union(aSet, bSet)
                    val calcLiveOut = foldl perSet LS.empty (map (getInOut nLIn) succs)

                    fun addEachOne(n, set) = LS.add(set, n)
                    val useSet = foldl addEachOne LS.empty (valOf (Flow.NodeMap.find(u, id)))
                    val defSet = foldl addEachOne LS.empty (valOf (Flow.NodeMap.find(d, id)))
                    val calcLiveIn = LS.union( useSet, (LS.difference(getInOut nLOut id, defSet)) )
                    

                    val FoundliveIn = getInOut nLIn id
                    val FoundliveOut = getInOut nLOut id

                    fun potentiallyaddnils dir x = case Flow.NodeMap.find(dir, x) of
                        SOME(res) => dir
                      | NONE => Flow.NodeMap.insert(dir,id,LS.empty)   
                    val newIn = if LS.equal(FoundliveIn, calcLiveIn) then (potentiallyaddnils nLIn id) else (change := true;(*print("~~~~~adding to in: "); printList(calcLiveIn);*) Flow.NodeMap.insert(nLIn, id, calcLiveIn))
                    val newOut = if LS.equal(FoundliveOut, calcLiveOut) then (potentiallyaddnils nLOut id) else (change := true;Flow.NodeMap.insert(nLOut, id, calcLiveOut))

                in
                    (newIn, newOut)
                end
            val (rIn, rOut) = foldl lives (liveIn, liveOut) nodeList 
        in
            if !change then doLive(g, rIn, rOut) else (rIn, rOut)
        end
        
    and makeEdges(liveOut, c, g) =
        let
            val nodeList = G.nodes(c)
            fun perNode(n, gr) = 
                let
                    val inst = G.nodeInfo(n)
                    val (src, dst) = case inst of 
                        Assem.MOVE{assem=_, src=s, dst=d} => (([s], [d]))
                      | Assem.OPER{assem=_, src=s, dst=d, jump=_} => (([], d))
                      | _ => ([], [])

                    val liveOuts = LS.listItems (valOf (Flow.NodeMap.find(liveOut, G.getNodeID(n))))
                    
                    fun perDest(dest_id, gra) =
                        let
                            val addList = difference liveOuts src
                            fun addEdge(tmp, grap) = G.doubleEdge(grap, dest_id, tmp)
                        in
                            foldl addEdge gra liveOuts
                        end
                in    
                    foldl perDest gr dst
                end
        in
            foldl perNode g nodeList
        end
    
    and getMoves(tnode, m ,c) =
        let
            val nodeList = G.nodes(c)
            fun perMove(a, lst) =
                let
                    val inst = G.nodeInfo(a)
                    val n_lst = case inst of
                        Assem.MOVE{assem=_, src=s, dst=d} => (tnode s, tnode d)::lst
                      | _ => lst
                in
                    n_lst
                end
        in
            foldl perMove [] nodeList
        end
    

    fun show (outstream,igraph) = 
        let
           val _ = print("\nInterference graph\n")
           val graph = case igraph of IGRAPH  {graph=g,tnode=t,gtemp=gt,moves=m} => g
           val _ = G.printGraph (fn (nodeid,temp) => "(Temp): t" ^ (Int.toString temp)) graph
        in
            ()
        end
end