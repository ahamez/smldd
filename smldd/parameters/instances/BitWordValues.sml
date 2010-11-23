structure BitWordValues : VALUES = struct

  (* User view *)
  type values             = BitWord.t

  val hash                = BitWord.hash
  val eq                  = BitWord.eq
  val length              = BitWord.length
  val empty               = BitWord.empty
  val toString            = BitWord.toString

  (* Library view *)
  type stored             = BitWord.t
  type value              = unit

  exception NotDiscrete
  val discrete            = false

  fun storedToList   _    = raise NotDiscrete
  fun storedFromList _    = raise NotDiscrete

  val mkStorable          = Util.id
  val mkUsable            = Util.id

  val storedEq            = BitWord.eq
  val storedLt            = BitWord.lt
  fun valueLt _           = raise NotDiscrete

  val storedHash          = BitWord.hash

  val storedEmpty         = BitWord.empty

  fun storedUnion []      = BitWord.mkEmpty ()
  |   storedUnion (x::xs) =
    foldl (fn (x,acc) => BitWord.union( x, acc ) ) x xs

  fun storedIntersection [] = BitWord.mkEmpty ()
  |   storedIntersection (x::xs) =
    foldl (fn (x,acc) => BitWord.intersection( x, acc )) x xs

  val storedDifference   = BitWord.difference

  val storedToString     = BitWord.toString

end
