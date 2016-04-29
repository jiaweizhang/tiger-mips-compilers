structure IntKey =
  struct
      type ord_key = int
      val compare = Int.compare
  end;


structure Temp : TEMP =
struct
  type temp = int
  val compare = Int.compare

  val labelCount = ref 0
  val temps = ref 100
  

  fun reset () = 
   let val () = temps := 100
     val () = labelCount := 0
   in
     ()
   end


  fun newtemp() = 
    let val t  = !temps 
      val () = temps := t+1
    in 
      t
    end
  fun makestring t = "t" ^ Int.toString t

  type label = Symbol.symbol

  structure TempOrd =
  struct 
    type ord_key = temp
    val compare = Int.compare
  end

  structure Set = SplaySetFn(TempOrd)
  structure Map = SplayMapFn(TempOrd)

  fun newlabel() = 
   let val x  = !labelCount
     val () = labelCount := x +1
   in
     Symbol.symbol ("L" ^ Int.toString(!labelCount))
   end
  
  val namedlabel = Symbol.symbol
   
   


end
