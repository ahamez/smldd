structure Hash =
struct

  type t = Word32.word

  val const       = Word32.fromInt
  val hashCombine = Word32.xorb
  val hashInt     = MLton.hash

  val toString    = Word32.toString

end (* structure Hash *)
