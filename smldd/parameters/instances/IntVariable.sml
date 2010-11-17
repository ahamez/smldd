structure IntVariable : VARIABLE =
struct

  type t        = Int32.int

  val eq        = op =
  val lt        = Int32.<
  val hash      = Hash.hashInt
  val toString  = Int32.toString

  val first     = 0
  fun next x    = x + 1

end
