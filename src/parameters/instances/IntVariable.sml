structure IntVariable : VARIABLE =
struct

  type t          = Int32.int

  fun eq(x,y)     = x = y
  fun hash x      = Word32.xorb( MLton.hash x, Word32.fromInt 666 )
  val toString    = Int32.toString

end
