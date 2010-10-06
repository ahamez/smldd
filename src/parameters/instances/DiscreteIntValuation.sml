structure DiscreteIntValuation : VALUATION =
struct

  (*----------------------------------------------------------------------*)
  type t  = IntVector.vector

  (*----------------------------------------------------------------------*)
  fun eq (l,r) =
    if (IntVector.length l) <> (IntVector.length r) then
      false
    else
      let
        fun helper 0 = true
        |   helper i =
          if IntVector.sub(l,i-1) = IntVector.sub(r,i-1) then
            helper (i - 1)
          else
            false
      in
        helper (IntVector.length l)
      end

  (*----------------------------------------------------------------------*)
  fun hash vec =
    let
      fun helper (x1,x2) = Word32.xorb ( MLton.hash x1, x2 )
    in
      IntVector.foldl helper (Word32.fromInt 42) vec
    end

  (*----------------------------------------------------------------------*)
  fun toString vec =
  let
    val l = map (fn x => Int32.toString x ) (IntVectorToList vec)
    val s = String.concatWith "|" l
  in
    "{" ^ s ^ "}"
  end

  (*----------------------------------------------------------------------*)
  val length = IntVector.length

  (*----------------------------------------------------------------------*)
  fun empty vec = IntVector.length vec = 0

  (*----------------------------------------------------------------------*)
  fun mkEmpty vec = IntVector.fromList []

  (*----------------------------------------------------------------------*)
  (* s1 and s2 MUST already be sorted *)
  fun union (s1,s2) =
    if IntVector.length s1 = 0 then
      s2
    else if IntVector.length s2 = 0 then
      s1
    else
      let
        val s1_head = IntVector.sub( s1, 0)
        val s2_head = IntVector.sub( s2, 0)
      in
        if s1_head > s2_head then
          IntVector.concat( [ IntVector.fromList([s2_head])
                         , union( s1, IntVectorSlice.vector(
                                        IntVectorSlice.slice( s2, 1, NONE))
                                )
                         ]
                       )
        else if s1_head < s2_head then
          IntVector.concat( [ IntVector.fromList([s1_head])
                         , union( s2, IntVectorSlice.vector(
                                        IntVectorSlice.slice( s1, 1, NONE))
                                )
                         ]
                       )
        else
          IntVector.concat( [ IntVector.fromList([s1_head])
                         , union( IntVectorSlice.vector(
                                    IntVectorSlice.slice( s1, 1, NONE))
                                , IntVectorSlice.vector(
                                    IntVectorSlice.slice( s2, 1, NONE))
                                )
                         ]
                       )
      end

  (*----------------------------------------------------------------------*)
  (* s1 and s2 MUST already be sorted *)
  fun intersection (s1,s2) =
    if IntVector.length s1 = 0 then
      s1
    else if IntVector.length s2 = 0 then
      s2
    else
      let
        val s1_head = IntVector.sub( s1, 0)
        val s2_head = IntVector.sub( s2, 0)
      in
        if s1_head = s2_head then
          IntVector.concat( [ IntVector.fromList([s1_head])
                         , intersection( IntVectorSlice.vector(
                                          IntVectorSlice.slice( s1, 1, NONE))
                                       , IntVectorSlice.vector(
                                          IntVectorSlice.slice( s2, 1, NONE))
                                       )
                         ]
                       )
        else if s1_head < s2_head then
          intersection( s2, IntVectorSlice.vector(
                              IntVectorSlice.slice( s1, 1, NONE))
                      )
        else
          intersection( s1, IntVectorSlice.vector(
                              IntVectorSlice.slice( s2, 1, NONE))
                      )
      end

  (*----------------------------------------------------------------------*)
  (* s1 and s2 MUST already be sorted *)
  fun difference (s1,s2) =
    if IntVector.length s1 = 0 orelse IntVector.length s2 = 0 then
      s1
    else
      let
        val s1_head = IntVector.sub( s1, 0)
        val s2_head = IntVector.sub( s2, 0)
      in
        if s1_head = s2_head then
          difference( IntVectorSlice.vector(IntVectorSlice.slice(s1,1,NONE))
                    , IntVectorSlice.vector(IntVectorSlice.slice(s2,1,NONE))
                    )
        else if s1_head < s2_head then
          IntVector.concat( [ IntVector.fromList([s1_head])
                         , difference( IntVectorSlice.vector(
                                        IntVectorSlice.slice( s1, 1, NONE))
                                     , s2
                                     )
                         ]
                       )
        else
          difference( s1, IntVectorSlice.vector(
                            IntVectorSlice.slice( s2, 1, NONE))
                    )
      end

  (*----------------------------------------------------------------------*)

end (* DiscreteIntValuation *)
