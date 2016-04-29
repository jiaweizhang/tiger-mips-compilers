signature COLOR =
sig
    type allocation = MipsFrame.register Temp.Map.map
    val color: {interference: Liveness.igraph,
                initial: allocation,
                spillCost: Temp.temp G.node -> int,
                registers: MipsFrame.register list}
               -> allocation * Temp.temp list
end
structure Color : COLOR =
struct 
type allocation = MipsFrame.register Temp.Map.map

fun color ({interference=interference,initial=initial,spillCost=spillCost,registers=registers}) =
  let
      val (graph,tnode,gtemp,moves) = case interference of Liveness.IGRAPH{graph=gr,tnode=tn,gtemp=gt,moves=m} => (gr,tn,gt,m)
      fun isPrecolored node = Utils.contains(G.nodeInfo node, map #1 (Temp.Map.listItemsi initial))

      (*Produces a potentially spilled node. This is a node still not in the stack, even after iterative simplifying. To do this,
            we find a node in the graph that are 1) not in the stack and 2) not precolored.
            Returns: SOME node (if there is a spill). NONE if no spill*)
      fun spilledNode(stack, spills) = 
        let
            val nodeList = G.nodes graph
            fun isOnStack node = Utils.contains(G.getNodeID node, map G.getNodeID stack)
            fun isSpilled node = Utils.contains(G.getNodeID node, map G.getNodeID spills)
            val spilledNodes = List.filter (fn node => (not (isPrecolored node)) andalso (not (isOnStack node)) andalso (not (isSpilled node))) nodeList
        in
            if List.length spilledNodes = 0 then NONE else SOME (List.nth(spilledNodes,0))
        end
            
      (*Produces a stack of removed nodes. Does so by continually running, removing nodes from the graph, until the stack doesn't grow in size.
              IE, when no more nodes can be removed. *)
      fun simplify (graph) = 
        let 
            (*Runs a round of simplifying. This will add all nodes with small degree to the stack, and remove them from the graph for later rounds. *)
            fun simplifyRound (initial_graph,initial_stack) = 
              let
                  fun simplifyPerNode(node,stack) = if G.degree(node) < 25 then node::stack else stack
                  val new_stack = foldl simplifyPerNode initial_stack (List.filter (fn x=> not (isPrecolored x)) (G.nodes initial_graph))
                  fun remove(node,graph) = G.removeNode'(graph,G.getNodeID node)
                  val newgraph = foldl remove initial_graph new_stack
              in
                  (*The round removed a node if these lengths are equal. If so, we should do another round to make sure that that removal doesn't propagate
                                into more nodes that need to be removed. IE: A node is removed, so the neighboring nodes have 1 degree less, so they may be candidates
                                for removal. m*)
                  if (List.length initial_stack = List.length new_stack) then (initial_graph,initial_stack) else simplifyRound (newgraph,new_stack)
              end
            val (new_graph, new_stack) = simplifyRound(graph,[])
        in
            new_stack
        end

      (*Given a graph and a list of spills, this will 1) run simplify until no more nodes can be removed. 2) Check if there are any nodes
              remaining that weren't removed because their degree is too high. 3) If there is a spill, rerun simplify. Otherwise, we're done. *)
      fun simplifyAndSpill (initial_stack,graph,spills) =
        let
            val stack = simplify (graph)
            val spilled_opt = spilledNode(stack, spills)
            val spilled_bool = isSome spilled_opt
            val new_graph = if spilled_bool then G.removeNode(graph,G.getNodeID (valOf spilled_opt)) else graph
        in
            if spilled_bool then simplifyAndSpill(initial_stack@stack,new_graph,(valOf spilled_opt)::spills) else (initial_stack@stack,spills) 
        end
            
      val (stack,potential_spilt_nodes) = simplifyAndSpill([],graph,[]) 
      (*After simplifying is finished, we have a stack of nodes that need to be colored. This will *)
      fun createAllocation(map,stack) = 
        let
            val unallocableNodes = ref []
            (*Given a node, and a current allocation map, returns a F.register that is both valid (no neighbors in the graph have it) and *)
            fun getColor(node,allocation) =
              let
                  (*Given a list of colors that are off-limits, and a list of possible registers, find the first register that isn't off-limits.*)
                  fun findFirstColorAvailable(unavailable_colors,r::regs) = if isSome (List.find (fn x => x = r) unavailable_colors) then findFirstColorAvailable(unavailable_colors,regs) else r
                    | findFirstColorAvailable(unavailable_colors,[]) = "NONE"
                  (*A list of all the registers already in use by neighbors of the node parameter.*)
                  fun neighborsColors(node) = List.mapPartial (fn neighbor => Temp.Map.find(allocation,neighbor)) (G.succs(node))
                  (* Neighbor node colors are off limits, and registers is all the registers. I reverse it so the first register grabbed is like t9/t8 rather than v0. (If you look at MipsFrame.registers, that's the order they come in). *)                            
                  val assigned_register = findFirstColorAvailable(neighborsColors(node),List.rev registers)                           
              in
                  assigned_register
              end
            (*Inserts the item StackNode -> (Calculated Color for Stack Node) into the Temp.Map.map AKA the allocation. *)
            fun allocateNodeAColor(stackNode,map) = 
              let
                  val assigned_register = getColor(stackNode,map)
              in
                  (*If node can be assigned a register, add it to the map and return the map! If not, IE when this is a spilt node, then side effect it into a list, return original map. *)
                  if assigned_register <> "NONE" then (Temp.Map.insert(map,G.nodeInfo stackNode,assigned_register)) else ((unallocableNodes:=(stackNode::(!unallocableNodes)); map))
              end
            (* Precolored nodes will not be considered for allocating, they're already colored! These are nodes in the stack whose temps are already in the map.*)
            val stackNodesThatArentAlreadyColored = (List.filter (fn node => not (isSome (Temp.Map.find(map,G.nodeInfo node)))) stack)
        in
            (*This is a map where all the temps are mapped to registers. *)
            (foldl allocateNodeAColor map stackNodesThatArentAlreadyColored,!unallocableNodes)
        end
      (*A map that has allocated everything on the stack. This does not allocate spilt nodes.*)
      val (allocation_of_stack,_) = createAllocation(initial,stack)
      (*Time to see if the potential spills are actual spills. The ability to reuse the createAllocation is a thing of beauty. *)
      val (allocation,actual_spills) = createAllocation(allocation_of_stack, potential_spilt_nodes)
      (*actual_spills is a list of spilt nodes. We need a list of spilt temps. *)
      val spills = map G.nodeInfo actual_spills
		       
  in
      (*Creates an allocation, using the "initial" allocation AKA the map with the precolored nodes. *)
      (allocation,spills) 
  end
end
