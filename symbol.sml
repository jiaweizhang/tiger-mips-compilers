signature SYMBOL =
sig
    eqtype symbol
    val symbol : string -> symbol
    val name : symbol -> string
    
    val hashtable : (string,int) HashTable.hash_table
    
    type 'a table
    val empty : 'a table
    val enter : 'a table * symbol * 'a -> 'a table
    val look : 'a table * symbol -> 'a option
end

   
structure Key =
struct
    type ord_key = int
    val compare = Int.compare
end

structure Map = SplayMapFn (Key)

structure Symbol : SYMBOL =
struct
    type symbol = string * int
    
    exception Symbol
    val nextsym = ref 0
    val hashtable : (string,int) HashTable.hash_table =
        HashTable.mkTable(HashString.hashString, op = ) (128,Symbol)
    fun symbol name =
        case HashTable.find hashtable name
            of SOME i => (name,i)
              | NONE => let val i = !nextsym
                          in nextsym := i+1;
                             HashTable.insert hashtable(name,i);
                             (name,i)
                        end
    fun name(s,n) = s
    
    type 'a table = 'a Map.map
    val empty = Map.empty
    fun enter(t: 'a table, (s,n): symbol, a: 'a) = Map.insert(t,n,a)
    fun look(t: 'a table, (s,n): symbol) = Map.find(t,n)
end

