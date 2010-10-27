structure IntVariable : VARIABLE =
struct

  type t          = Int32.int

  fun eq(x,y)     = x = y
  fun hash x      = Hash.hashCombine( Hash.hashInt x, Hash.const 666 )
  val toString    = Int32.toString

  val first       = 0
  fun next x      = x + 1

end
