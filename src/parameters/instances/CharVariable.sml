structure CharVariable : VARIABLE =
struct
  
  type t          = Char.char
  
  fun eq(x,y)     = x = y
  val lt          = Char.<
  val hash        = MLton.hash
  val toString    = Char.toString
  
end
