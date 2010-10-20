structure Hash =
struct

  type t = Word32.word

  val const       = MLton.hash

  val hashInt     = MLton.hash
  val hashWord    = MLton.hash

  fun hashCombine ( seed , v ) =
  let
    val res = v
            + (Word32.fromLargeInt 0x9e3779b9)
            + (Word32.>>( seed, Word32.fromInt 6 ))
            + (Word32.>>( seed, Word32.fromInt 2 ))
  in
    Word32.xorb( seed, res )
  end

end (* structure Hash *)
