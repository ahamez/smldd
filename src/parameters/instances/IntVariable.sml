structure IntVariable : VARIABLE =
struct

  type t          = Int32.int

  fun eq(x,y)     = x = y
  val lt          = Int32.<
  val hash        = MLton.hash
  val toString    = Int32.toString

end
