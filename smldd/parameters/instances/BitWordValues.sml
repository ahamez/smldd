structure BitWordValues : VALUES = struct

  (* User view *)
  type values             = BitWord.t

  val hash                = BitWord.hash
  val eq                  = BitWord.eq
  val length              = BitWord.length
  val empty               = BitWord.empty
  val toString            = BitWord.toString

  fun union []      = BitWord.mkEmpty ()
  |   union (x::xs) = foldl (fn (x,acc) => BitWord.union( x, acc ) ) x xs

  fun intersection [] = BitWord.mkEmpty ()
  |   intersection (x::xs) =
    foldl (fn (x,acc) => BitWord.intersection( x, acc )) x xs

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

  val storedUnion         = union

  val storedIntersection  = intersection

  val storedDifference   = BitWord.difference

  val storedToString     = BitWord.toString

end
