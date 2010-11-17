structure Hash =
struct

  type t = Word32.word

  (* Taken from murmurHash2 *)
  fun hashWord x =
  let
    val m = 0wx5bd1e995
    val r = Word32.fromInt 24
    val h0 = Word32.xorb( x, 0wx9e3779b9)
    val k0 = x * m
    val k1 = Word32.xorb( k0, Word32.>>( k0, r) )
    val k2 = k1 * m
    val h1 = h0 * m
    val h2 = Word32.xorb( h1, k2 )
  in
    h2
  end

  val hashInt = hashWord o Word32.fromInt

  (* Taken from boost::hash_combine *)
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
