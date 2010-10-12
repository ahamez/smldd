structure TestSDD =
struct

  (* ---------------------------------------------------------------- *)
  
  open SDD
  open SMLUnit.Assert
  structure Test = SMLUnit.Test

  (* ---------------------------------------------------------------- *)

  val values = Values o IntVector.fromList

  fun testTerminal00 () =
    assertTrue( zero <> one )

  fun testMknode00 () =
    assertTrue( node( 0, values [] , one  ) = zero )

  fun testMknode01 () =
    assertTrue( node( 0, values [0], zero ) = zero )

  fun testMknode02 () =
    assertTrue( node( 0, values [] , zero ) = zero )

  fun testFlatUnion00 () =
  let
    val s0 = node( 0, values [1,2,3], one )
    val s1 = node( 0, values [0,2,3], one )
    val u0 = union [s0,s1]
    val o0 = node( 0, values [0,1,2,3], one)
  in
    assertTrue( u0 = o0 )
  end

  fun testFlatUnion01 () =
  let
    val s0 = node( 1, values [1,2,3], one )
    val s1 = node( 0, values [0,2,3], one )
  in
    ( union [s0,s1] ; fail "Must fail" )
    handle x as _ => assertEqualExceptionName x IncompatibleSDD
  end

  fun testFlatUnion02 () =
  let
    val s0 = node( 1, values [1,2,3], one )
  in
    ( union [s0,one] ; fail "Must fail" )
    handle x as _ => assertEqualExceptionName x IncompatibleSDD
  end

  fun testFlatUnion03 () =
  let
    val s0 = node( 0, values [1,2,3], one )
    val u0 = union [s0,zero]
  in
    assertTrue( u0 = s0 )
  end

  fun testFlatUnion04 () =
  let
    val s0 = node( 0, values [1,2,3], one )
    val s1 = node( 0, values [0,2,3], one )
    val s2 = node( 0, values [0,666], one )
    val s3 = node( 0, values [42,43,44], one )
    val s4 = node( 0, values [0], one )
    val s5 = node( 0, values [~273,17,33], one )
    val u0 = union [s0,s1,s2,s3,s4,s5]
    val o0 = node( 0, values [~273,0,1,2,3,17,33,42,43,44,666], one)
  in
    assertTrue( u0 = o0 )
  end

  fun testFlatUnion05 () =
  let
    val s0 = node( 0, values [1,2,3], one )
    val s1 = node( 0, values [0,2,3], one )
    val s2 = node( 0, values [0,666], one )
    val s3 = node( 0, values [42,43,44], one )
    val s4 = node( 0, values [0], one )
    val s5 = node( 0, values [~273,17,33], one )
  in
    ( union [s0,s1,s2,s3,s4,s5,one] ; fail "Must fail" )
    handle x as _ => assertEqualExceptionName x IncompatibleSDD
  end

  fun testFlatUnion06 () =
  let
    val s0 = node( 0, values [1,2,3], one )
    val s1 = node( 0, values [0,2,3], one )
    val s2 = node( 1, values [0], s0)
    val s3 = node( 1, values [0], s1)
    val u0 = union [s2,s3]
    val o0 = node( 1, values [0]
                     , node( 0, values [0,1,2,3], one )
                     )
  in
    assertTrue( u0 = o0 )
  end

  fun testFlatUnion07 () =
  let
    val s0 = node( 0, values [1,2,3], one )
    val u0 = union [s0,s0]
  in
    assertTrue( u0 = s0 )
  end

  fun testFlatUnion08 () =
  let
    val s0 = node( 0, values [0,1], one )
    val s2 = node( 1, values [0,1], s0  )
    val s1 = node( 0, values [2,3], one )
    val s3 = node( 1, values [2,3], s1  )
    val u0 = union [s2,s3]

    val s4 = node( 0, values [0,1], one )
    val s5 = node( 1, values [0],   s4  )
    val s6 = node( 0, values [1],   one )
    val s7 = node( 1, values [0],   s6  )
    val s8 = node( 0, values [2,3], one )
    val s9 = node( 1, values [2,3], s8  )
    val u1 = union [s5,s7,s9]

    val s10 = node( 0, values [0,1], one )
    val s11 = node( 1, values [0,1], s10 )
    val s12 = node( 0, values [2,3], one )
    val s13 = node( 1, values [2],   s12 )
    val s14 = node( 0, values [2],   one )
    val s15 = node( 1, values [3],   s14 )
    val u2 = union [s11,s13,s15]

    val u3 = union [u1,u2]
  in
    assertTrue( u0 = u3 )
  end

  fun testFlatUnion09 () =
  let
    val s0 = node( 1, values [0,1],
               node( 0, values [0,1], one))
    val s1 = node( 1, values [2,3],
               node( 0, values [2,3], one))
    val u0 = union [s0,s1]

    val s2 = node( 1, values [0],
               node( 0, values [1], one))
    val u2 = union [u0,s2]
  in
    assertTrue( u0 = u2 )
  end

  fun testFlatUnion10 () =
  let
    val s0 = node( 0, values [1,2,3], one )
    val u0 = union [s0,s0,s0,s0,s0,s0,s0]
  in
    assertTrue( u0 = s0 )
  end

  fun testFlatUnion11 () =
  let
    val s10 = node( 0, values [0,1], one )
    val s11 = node( 1, values [0,1], s10 )
    val s12 = node( 0, values [2,3], one )
    val s13 = node( 1, values [2],   s12 )
    val s14 = node( 0, values [2],   one )
    val s15 = node( 1, values [3],   s14 )
    val u2 = union [s11,s13,s15]
    val u3 = union [s13,s15,s11]
  in
    assertTrue( u2 = u3 )
  end

  fun testFlatUnion12 () =
  let
    val s0 = node( 0, values [0,1], one )
    val s2 = node( 1, values [0,1], s0  )
    val s1 = node( 0, values [2,3], one )
    val s3 = node( 1, values [2,3], s1  )
    val u0 = union [s2,s3]
    val u1 = union [s3,s2]
  in
    assertTrue( u0 = u1 )
  end

  fun testFlatUnion13 () =
  let
    val s4 = node( 0, values [0,1], one )
    val s5 = node( 1, values [0],   s4  )
    val s6 = node( 0, values [1],   one )
    val s7 = node( 1, values [0],   s6  )
    val s8 = node( 0, values [2,3], one )
    val s9 = node( 1, values [2,3], s8  )
    val u1 = union [s5,s7,s9]
    val u2 = union [s7,s5,s9]
  in
    assertTrue( u1 = u2 )
  end

  fun testFlatUnion14 () =
  let
    val s1 = node( 0, values [0],
              node( 1, values [0],
               node( 2, values [1],
                node( 3, values [1],
                 node( 4, values [1], one)))))
    val s3 = node( 0, values [0],
              node( 1, values [1],
               node( 2, values [1],
                node( 3, values [1],
                 node( 4, values [0], one)))))

    val s5 = node( 0, values [0],
              node( 1, values [2],
               node( 2, values [1],
                node( 3, values [0],
                 node( 4, values [0], one)))))

    val s8 = union [s1,s3,s5]
    val s9 = union [s3,s1,s5]

  in
    assertTrue( s8 = s9 )
  end

  fun testFlatInter00 () =
  let
    val s0 = node( 0, values [1,2,3], one )
    val s1 = node( 0, values [0,2,3], one )
    val i1 = intersection [s0,s1]
    val o0 = node( 0, values [2,3], one )
  in
    assertTrue( i1 = o0 )
  end

  fun testFlatInter01 () =
  let
    val s0 = node( 0, values [1,2,3], one )
    val i1 = intersection [s0,zero]
  in
    assertTrue( i1 = zero )
  end

  fun testFlatInter02 () =
  let
    val s0 = node( 0, values [1,2,3], one )
    val i1 = intersection [s0,s0]
  in
    assertTrue( i1 = s0 )
  end

  fun testFlatInter03 () =
  let
    val s0 = node( 1, values [1,2,3], one )
    val s1 = node( 0, values [0,2,3], one )
  in
    ( intersection [s0,s1] ; fail "Must fail" )
    handle x as _ => assertEqualExceptionName x IncompatibleSDD
  end

  fun testFlatInter04 () =
  let
    val s0 = node( 42, values [1,2,4], one )
  in
    ( intersection [one,s0] ; fail "Must fail" )
    handle x as _ => assertEqualExceptionName x IncompatibleSDD
  end

  fun testFlatInter05 () =
  let
    val s0 = node( 42, values [0,1,2,3], one )
    val s1 = node( 42, values [4,5,6,7], one )
    val i0 = intersection [s0, s1]
  in
    assertTrue( i0 = zero )
  end

  fun testFlatInter06 () =
  let
    val s0 = node( 42, values [0,1,2,3], one )
    val s1 = node( 42, values [4,5,6,7], one )
    val s2 = node( 0, values [0], s0 )
    val s3 = node( 0, values [0], s1 )
    val i0 = intersection [s2, s3]
  in
    assertTrue( i0 = zero )
  end

  fun testFlatInter07 () =
  let
    val s0 = node( 0, values [0,1,2,3], one )
    val s1 = node( 0, values [4,5,6,7], one )
    val s2 = node( 1, values [1], s0 )
    val s3 = node( 1, values [0], s1 )
    val u0 = union [s2, s3]

    val s4 = node( 0, values [17,23], one )
    val s5 = node( 0, values [42,66], one )
    val s6 = node( 1, values [1], s4 )
    val s7 = node( 1, values [0], s5 )
    val u1 = union [s6, s7]

    val i0 = intersection [u0,u1]
  in
    assertTrue( i0 = zero )
  end

  fun testFlatInter08 () =
  let
    val s0 = node( 0, values [0,1,2,3], one )
    val s1 = node( 0, values [4,5,6,7], one )
    val s2 = node( 1, values [1], s0 )
    val s3 = node( 1, values [0], s1 )
    val u0 = union [s2, s3]

    val s4 = node( 0, values [0,17,23], one )
    val s5 = node( 1, values [1], s4 )

    val i0 = intersection [s5,u0]
    val o0 = node( 1, values [1]
                     , node( 0, values [0], one ) )

  in
    assertTrue( i0 = o0 )
  end

  fun testFlatInter09 () =
  let
    val s0 = node( 0, values [0], one )
    val s2 = node( 1, values [1], s0 )

    val s4 = node( 0, values [0], one )
    val s5 = node( 0, values [2], one )
    val s6 = node( 1, values [1], s4 )
    val s7 = node( 1, values [0], s5 )
    val u1 = union [s6, s7]

    val i0 = intersection [s2,u1]
    val o0 = node( 1, values [1]
                     , node( 0, values [0], one ) )
  in
    assertTrue( i0 = o0 )
  end

  fun testFlatInter10 () =
  let
    val s0 = node( 0, values [0,1,2,3], one )
    val s1 = node( 0, values [4,5,6,7], one )
    val s2 = node( 1, values [1], s0 )
    val s3 = node( 1, values [0], s1 )
    val u0 = union [s2, s3]

    val s4 = node( 0, values [0,17,23], one )
    val s5 = node( 0, values [42,66], one )
    val s6 = node( 1, values [1], s4 )
    val s7 = node( 1, values [0], s5 )
    val u1 = union [s6, s7]

    val i0 = intersection [u1,u0]
    val o0 = node( 1, values [1]
                     , node( 0, values [0], one ) )
  in
    assertTrue( i0 = o0 )
  end

  fun testFlatInter11 () =
    assertTrue( intersection [one,one] = one )

  fun testFlatInter12 () =
    assertTrue( intersection [one,zero] = zero )

  fun testFlatInter13 () =
  let
    val s0 = node( 0, values [0,1,2,3], one )
    val s1 = node( 0, values [4,5,6,7], one )
    val s2 = node( 0, values [8,9,10],  one )
    val s3 = node( 1, values [1], s0 )
    val s4 = node( 1, values [0], s1 )
    val s5 = node( 1, values [2], s2 )
    val u0 = union [ s3, s4, s5 ]

    val s6 = node( 0, values [0,17,23], one )
    val s7 = node( 0, values [42,66], one )
    val s8 = node( 0, values [8,127], one )
    val s9 = node( 1, values [1], s6 )
    val s10 = node( 1, values [0], s7 )
    val s11 = node( 1, values [2], s8 )
    val u1 = union [ s9, s10, s11 ]

    val i0 = intersection [u1,u0]
    val o0 = union[
               node( 1, values [1]
                       , node( 0, values [0], one ) )
             , node( 1, values [2]
                       , node( 0, values [8], one ) )
             ]
  in
    assertTrue( i0 = o0 )
  end

  fun testFlatInter14 () =
  let
    val s0 = node( 0, values [0,1], one )
    val s1 = node( 0, values [0,2], one )
    val s2 = node( 1, values [0,3], s0 )
    val s3 = node( 1, values [0,4], s1 )
    val s4 = node( 2, values [0], s2 )
    val s5 = node( 2, values [1], s3 )
    val u0 = union [ s4, s5 ]

    val s6 = node( 0, values [0,3], one )
    val s7 = node( 0, values [0,4], one )
    val s8 = node( 1, values [0,5], s6 )
    val s9 = node( 1, values [0,6], s7 )
    val s10 = node( 2, values [0], s8 )
    val s11 = node( 2, values [1], s9 )
    val u1 = union [ s10, s11 ]

    val i0 = intersection [u1,u0]
    val o0 = node( 2, values [0,1]
               , node( 1, values [0]
                 ,  node( 0, values [0], one )))

  in
    assertTrue( i0 = o0 )
  end

  fun testFlatInter15 () =
  let
    val s0 = node( 0, values [0,1], one )
    val s1 = node( 0, values [0,2], one )
    val s2 = node( 1, values [0,3], s0 )
    val s3 = node( 1, values [0,4], s1 )
    val s4 = node( 2, values [0], s2 )
    val s5 = node( 2, values [1], s3 )
    val u0 = union [ s4, s5 ]

    val s6 = node( ~1, values [0,3], one )
    val s7 = node( ~1, values [0,4], one )
    val s8 = node( 1, values [0,5], s6 )
    val s9 = node( 1, values [0,6], s7 )
    val s10 = node( 2, values [0], s8 )
    val s11 = node( 2, values [1], s9 )
    val u1 = union [ s10, s11 ]
  in
    ( intersection [u0,u1] ; fail "Must fail" )
    handle x as _ => assertEqualExceptionName x IncompatibleSDD
  end

  fun testFlatDiff00 () =
  let
    val d0 = difference( one, one )
  in
    assertTrue( d0 = zero )
  end

  fun testFlatDiff01 () =
  let
    val s0 = node( 0, values [0,1,2,3], one )
    val s1 = node( 0, values [4,5,6,7], one )
    val d0 = difference( s1, s0 )
  in
    assertTrue( d0 = s1 )
  end

  fun testFlatDiff02 () =
  let
    val s0 = node( 0, values [0,1,2,3], one )
    val s1 = node( 0, values [4,5,6,7], one )
    val d0 = difference( s0, s1 )
  in
    assertTrue( d0 = s0 )
  end

  fun testFlatDiff03 () =
  let
    val s0 = node( 0, values [0,1,2,3], one )
    val s1 = node( 0, values [0,3], one )
    val d0 = difference( s0, s1 )
    val o0 = node( 0, values [1,2], one )
  in
    assertTrue( d0 = o0 )
  end

  fun testFlatDiff04 () =
  let
    val s0 = node( 0, values [0,1,2,3], one )
    val s1 = node( 0, values [0,3], one )
    val d0 = difference( s1, s0 )
  in
    assertTrue( d0 = zero )
  end

  fun testFlatDiff05 () =
  let
    val s0 = node( 0, values [0,1,2,3], one )
    val s1 = node( 0, values [0,4], one )
    val d0 = difference( s1, s0 )
    val o0 = node( 0, values [4], one )
  in
    assertTrue( d0 = o0 )
  end

  fun testFlatDiff06 () =
  let
    val s0 = node( 0, values [0], one )
    val s1 = node( 0, values [0], one )
    val s2 = node( 1, values [0], s0  )
    val s3 = node( 1, values [1], s1  )
    val u0 = union [s2,s3]
    val d0 = difference( u0, s2 )
  in
    assertTrue( d0 = s3 )
  end

  fun testFlatDiff07 () =
  let
    val s0 = node( 0, values [0], one )
    val s1 = node( 0, values [0], one )
    val s2 = node( 1, values [0], s0  )
    val s3 = node( 1, values [1], s1  )
    val u0 = union [s2,s3]
    val d0 = difference( u0, s3 )
  in
    assertTrue( d0 = s2 )
  end

  fun testFlatDiff08 () =
  let
    val s0 = node( 0, values [0], one )
    val s1 = node( 1, values [0], one )
  in
    ( difference( s1, s0 ) ; fail "Must fail" )
    handle x as _ => assertEqualExceptionName x IncompatibleSDD
  end

  fun testFlatDiff09 () =
  let
    val s0 = node( 0, values [0], one )
    val s1 = node( 1, values [0], one )
  in
    ( difference( s0, s1 ) ; fail "Must fail" )
    handle x as _ => assertEqualExceptionName x IncompatibleSDD
  end

  fun testFlatDiff10 () =
  let
    val s0 = node( 0, values [0], one )
  in
    ( difference( s0, one ) ; fail "Must fail" )
    handle x as _ => assertEqualExceptionName x IncompatibleSDD
  end

  fun testFlatDiff11 () =
  let
    val s0 = node( 0, values [0], one )
  in
    ( difference( one, s0 ) ; fail "Must fail" )
    handle x as _ => assertEqualExceptionName x IncompatibleSDD
  end

  fun testFlatDiff12 () =
  let
    val s0 = node( 0, values [0], one )
    val d0 = difference( s0, zero )
  in
    assertTrue( d0 = s0 )
  end

  fun testFlatDiff13 () =
  let
    val s0 = node( 0, values [0], one )
    val d0 = difference( zero, s0 )
  in
    assertTrue( d0 = zero )
  end

  fun testFlatDiff14 () =
  let
    val d0 = difference( zero, one )
  in
    assertTrue( d0 = zero )
  end

  fun testFlatDiff15 () =
  let
    val d0 = difference( one, zero )
  in
    assertTrue( d0 = one )
  end

  fun testFlatDiff16 () =
  let
    val s0 = node( 0, values [0,1], one )
    val s2 = node( 1, values [0,1], s0  )
    val s4 = node( 2, values [0,1], s2  )
    val s1 = node( 0, values [2,3], one )
    val s3 = node( 1, values [2,3], s1  )
    val s5 = node( 2, values [2,3], s3  )
    val u0 = union [s4,s5]

    val s7  = node( 0, values [0], one )
    val s9  = node( 1, values [0], s7  )
    val s10 = node( 2, values [0], s9  )
    val s11 = node( 0, values [3], one )
    val s12 = node( 1, values [3], s11 )
    val s13 = node( 2, values [3], s12 )
    val u1 = union [s10,s13]

    val d0 = difference ( u0, u1 )

    val o0 = union
             [ node( 2, values [0],
                 node( 1, values [0,1],
                   node( 0, values [1], one)))
             , node( 2, values [0],
                 node( 1, values [1],
                   node( 0, values [0,1], one)))
             , node( 2, values [1],
                 node( 1, values [0,1],
                   node( 0, values [0,1], one)))
             , node( 2, values [3],
                 node( 1, values [2,3],
                   node( 0, values [2], one)))
             , node( 2, values [3],
                 node( 1, values [2],
                   node( 0, values [2,3], one)))
             , node( 2, values [2],
                 node( 1, values [2,3],
                   node( 0, values [2,3], one)))
             ]
  in
    assertTrue( d0 = o0 )
  end

  fun testFlatDiff17 () =
  let
    val s0 = node( 0, values [0,1], one )
    val s1 = node( 0, values [0,3], one )
    val s2 = node( 1, values [0,1], s0  )
    val s3 = node( 1, values [0,2], s1  )
    val s4 = node( 2, values [0,1], s2  )
    val s5 = node( 2, values [2,3], s3  )
    val u0 = union [s4,s5]

    val s7  = node( 0, values [0], one )
    val s9  = node( 1, values [0], s7  )
    val s11 = node( 2, values [0], s9  )

    val d0 = difference ( u0, s11 )

    val o0 = union
             [ node( 2, values [0],
                 node( 1, values [0,1],
                   node( 0, values [1], one)))
             , node( 2, values [0],
                 node( 1, values [1],
                   node( 0, values [0,1], one)))
             , node( 2, values [1],
                 node( 1, values [0,1],
                   node( 0, values [0,1], one)))
             , node( 2, values [2,3],
                 node( 1, values [0,2],
                   node( 0, values [0,3], one)))
             ]
  in
    assertTrue( d0 = o0 )
  end

  fun testFlatDiff18 () =
  let
    val s0 = node( 0, values [0,1], one )
    val s1 = node( 1, values [0,1], s0  )
    val s2 = node( 2, values [0,1], s1  )

    val s3 = node( 0, values [0], one )
    val s4 = node( 1, values [0], s3  )
    val s5 = node( 2, values [0], s4  )

    val d0 = difference ( s2, s5 )
    val o0 = union
             [ node( 2, values [0],
                 node( 1, values [0,1],
                   node( 0, values [1], one)))
             , node( 2, values [0],
                 node( 1, values [1],
                   node( 0, values [0,1], one)))
             , node( 2, values [1],
                 node( 1, values [0,1],
                   node( 0, values [0,1], one)))
             ]
  in
    assertTrue( d0 = o0 )
  end

  fun testFlatDiff19 () =
  let
    val s0 = node( 0, values [0,1], one )
    val s1 = node( 1, values [0,1], s0  )
    val s2 = node( 2, values [0,1], s1  )

    val s3 = node( 0, values [0], one )
    val s4 = node( 1, values [0], s3  )
    val s5 = node( 2, values [0], s4  )

    val d0 = difference ( s5, s2 )
  in
    assertTrue( d0 = zero )
  end

  fun testFlatDiff20 () =
  let
    val s0 = node( 0, values [0,1], one )
    val s1 = node( 0, values [0,3], one )
    val s2 = node( 1, values [0,1], s0  )
    val s3 = node( 1, values [0,2], s1  )
    val s4 = node( 2, values [0,1], s2  )
    val s5 = node( 2, values [2,3], s3  )
    val u0 = union [s4,s5]

    val s7  = node( 0, values [0], one )
    val s9  = node( 1, values [0], s7  )
    val s11 = node( 2, values [0], s9  )

    val d0 = difference ( s11, u0 )
  in
    assertTrue( d0 = zero )
  end

  fun testFlatDiff21 () =
  let
    val s0 = node( 0, values [0,1], one )
    val s1 = node( 0, values [2,3], one )
    val s2 = node( 1, values [0,1], s0  )
    val s3 = node( 1, values [2,3], s1  )
    val s4 = node( 2, values [0,1], s2  )
    val s5 = node( 2, values [2,3], s3  )
    val u0 = union [s4,s5]

    val s7  = node( 0, values [0], one )
    val s9  = node( 1, values [0], s7  )
    val s10 = node( 2, values [0], s9  )
    val s11 = node( 0, values [3], one )
    val s12 = node( 1, values [3], s11 )
    val s13 = node( 2, values [3], s12 )
    val u1 = union [s10,s13]

    val d0 = difference ( u1, u0 )
  in
    assertTrue( d0 = zero )
  end

  fun testFlatDiff23 () =
  let
    val s0 = node( 0, values [0,1], one )
    val s2 = node( 1, values [0,1], s0  )
    val s1 = node( 0, values [2,3], one )
    val s3 = node( 1, values [2,3], s1  )
    val u0 = union [s2,s3]

    val s7  = node( 0, values [0], one )
    val s9  = node( 1, values [0], s7  )
    val s11 = node( 0, values [3], one )
    val s12 = node( 1, values [3], s11 )

    val d0 = difference ( u0, s9  )
    val d1 = difference ( u0, s12 )
    val u1 = union [d0,d1]
  in
    assertTrue( u0 = u1 )
  end

  fun testFlatDiff24 () =
  let
    val s0 = node( 0, values [0,1], one )
    val s2 = node( 1, values [0,1], s0  )
    val s1 = node( 0, values [2,3], one )
    val s3 = node( 1, values [2,3], s1  )
    val u0 = union [s2,s3]

    val s7  = node( 0, values [0], one )
    val s9  = node( 1, values [0], s7  )
    val s11 = node( 0, values [3], one )
    val s12 = node( 1, values [3], s11 )
    val u1 = union [s9,s12]

    val d0 = difference ( u0, u1 )

    val o0 = union
             [ node( 1, values [0,1],
                 node( 0, values [1], one))
             , node( 1, values [1],
                 node( 0, values [0,1], one))
             , node( 1, values [2,3],
                 node( 0, values [2], one))
             , node( 1, values [2],
                 node( 0, values [2,3], one))
             ]
  in
    assertTrue( d0 = o0 )
  end

  fun testMkNode00 () =
    assertTrue( node( 0, Nested zero , one  ) = zero )

  fun testMkNode01 () =
    assertTrue( node( 0, Nested one, zero ) = zero )

  fun testMkNode02 () =
    assertTrue( node( 0, Nested (node( 1, Nested zero, one )), one ) = zero )

  fun testMkNode03 () =
    assertTrue( node( 0, Nested (node( 1, Nested zero, one )), zero ) = zero )

  fun testMkNode04 () =
    assertTrue( node( 0, Nested(node(1,values [1],zero)), one)
                = zero
              )

  fun testMkNode05 () =
    assertTrue( node( 0, Nested(node(1,values [],one)), one)
                = zero
              )

  fun testUnion00 () =
  let
    val s0 = node( 0, values [1,2,3], one )
    val x0 = node( 0, Nested s0, one )
    val s1 = node( 0, values [0,2,3], one )
    val x1 = node( 0, Nested s1, one )
    val u0 = union [x1,x0]
    val o0 = node( 0, values [0,1,2,3], one)
    val y0 = node( 0, Nested o0, one )
  in
    assertTrue( u0 = y0 )
  end

  fun testUnion01 () =
  let
    val s0 = node( 0, values [1,2,3], one )
    val x0 = node( 0, Nested s0, one )
    val u0 = union [x0,zero]
  in
    assertTrue( u0 = x0 )
  end

  fun testUnion02 () =
  let
    val s0 = node( 0, values [1,2,3], one )
    val x0 = node( 0, Nested s0, one )
    val u0 = union [x0,x0,x0,x0,x0]
  in
    assertTrue( u0 = x0 )
  end

  fun testUnion03 () =
  let
    val s0 = node( 0, values [1,2,3], one )
    val x0 = node( 0, Nested s0, one )
    val s1 = node( 1, values [0,2,3], one )
    val x1 = node( 0, Nested s1, one )
  in
    ( union [x0,x1] ; fail "Must fail" )
    handle x as _ => assertEqualExceptionName x IncompatibleSDD
  end

  fun testUnion04 () =
  let
    val s0 = node( 0, values [1,2,3], one )
    val x0 = node( 0, Nested s0, one )
    val s1 = node( 0, values [0,2,3], one )
    val x1 = node( 1, Nested s1, one )
  in
    ( union [x0,x1] ; fail "Must fail" )
    handle x as _ => assertEqualExceptionName x IncompatibleSDD
  end

  fun testUnion05 () =
  let
    val s0 = node( 0, values [1,2,3], one )
    val x0 = node( 0, Nested s0, one )
  in
    ( union [x0,one] ; fail "Must fail" )
    handle x as _ => assertEqualExceptionName x IncompatibleSDD
  end

  fun testUnion06 () =
  let
    val s0 = node( 0, values [1,2,3], one )
    val x0 = node( 0, Nested s0, one )
    val x1 = node( 1, Nested one, one )
  in
    ( union [x0,x1] ; fail "Must fail" )
    handle x as _ => assertEqualExceptionName x IncompatibleSDD
  end

  fun testUnion07 () =
  let
    val s0 = node( 0, values [1,2,3], one )
    val x0 = node( 0, Nested s0, one )
    val u0 = union [zero,x0,zero,x0,zero,x0,zero,x0,zero,x0,zero]
  in
    assertTrue( u0 = x0 )
  end

  fun testPaths00 () =
  let
    val s0 = node( 0, values [1],
              node( 1, values [2],
               node( 2, values [0],
                node( 3, values [0],
                 node( 4, values [0], one)))))
    val s1 = node( 0, values [0],
              node( 1, values [0],
               node( 2, values [1],
                node( 3, values [1],
                 node( 4, values [1], one)))))
    val s2 = node( 0, values [0],
              node( 1, values [1],
               node( 2, values [1],
                node( 3, values [0],
                 node( 4, values [1], one)))))
    val s3 = node( 0, values [0],
              node( 1, values [1],
               node( 2, values [1],
                node( 3, values [1],
                 node( 4, values [0], one)))))
    val s4 = node( 0, values [1],
              node( 1, values [0],
               node( 2, values [0],
                node( 3, values [1],
                 node( 4, values [1], one)))))
    val s5 = node( 0, values [0],
              node( 1, values [2],
               node( 2, values [1],
                node( 3, values [0],
                 node( 4, values [0], one)))))
    val s6 = node( 0, values [1],
              node( 1, values [1],
               node( 2, values [0],
                node( 3, values [0],
                 node( 4, values [1], one)))))
    val s7 = node( 0, values [1],
              node( 1, values [1],
               node( 2, values [0],
                node( 3, values [1],
                 node( 4, values [0], one)))))

    val s8 = union [s0,s1,s2,s3,s4,s5,s6,s7]

    val nb = paths s8
  in
    assertTrue( nb = 8 )
  end

  (* ---------------------------------------------------------------- *)

  fun suite () =
      Test.labelTests
      [ ("Terminals00"       , testTerminal00      )
      , ("Makenode00"        , testMknode00    )
      , ("Makenode01"        , testMknode01    )
      , ("Makenode02"        , testMknode02    )
      , ("FlatUnion00"       , testFlatUnion00     )
      , ("FlatUnion01"       , testFlatUnion01     )
      , ("FlatUnion02"       , testFlatUnion02     )
      , ("FlatUnion03"       , testFlatUnion03     )
      , ("FlatUnion04"       , testFlatUnion04     )
      , ("FlatUnion05"       , testFlatUnion05     )
      , ("FlatUnion06"       , testFlatUnion06     )
      , ("FlatUnion07"       , testFlatUnion07     )
      , ("FlatUnion08"       , testFlatUnion08     )
      , ("FlatUnion09"       , testFlatUnion09     )
      , ("FlatUnion10"       , testFlatUnion10     )
      , ("FlatUnion11"       , testFlatUnion11     )
      , ("FlatUnion12"       , testFlatUnion12     )
      , ("FlatUnion13"       , testFlatUnion13     )
      , ("FlatUnion14"       , testFlatUnion14     )
      , ("FlatInter00"       , testFlatInter00     )
      , ("FlatInter01"       , testFlatInter01     )
      , ("FlatInter02"       , testFlatInter02     )
      , ("FlatInter03"       , testFlatInter03     )
      , ("FlatInter04"       , testFlatInter04     )
      , ("FlatInter05"       , testFlatInter05     )
      , ("FlatInter06"       , testFlatInter06     )
      , ("FlatInter07"       , testFlatInter07     )
      , ("FlatInter08"       , testFlatInter08     )
      , ("FlatInter09"       , testFlatInter09     )
      , ("FlatInter10"       , testFlatInter10     )
      , ("FlatInter11"       , testFlatInter11     )
      , ("FlatInter12"       , testFlatInter12     )
      , ("FlatInter13"       , testFlatInter13     )
      , ("FlatInter14"       , testFlatInter14     )
      , ("FlatInter15"       , testFlatInter15     )
      , ("testFlatDiff00"    , testFlatDiff00      )
      , ("testFlatDiff01"    , testFlatDiff01      )
      , ("testFlatDiff02"    , testFlatDiff02      )
      , ("testFlatDiff03"    , testFlatDiff03      )
      , ("testFlatDiff04"    , testFlatDiff04      )
      , ("testFlatDiff05"    , testFlatDiff05      )
      , ("testFlatDiff06"    , testFlatDiff06      )
      , ("testFlatDiff07"    , testFlatDiff07      )
      , ("testFlatDiff08"    , testFlatDiff08      )
      , ("testFlatDiff09"    , testFlatDiff09      )
      , ("testFlatDiff10"    , testFlatDiff10      )
      , ("testFlatDiff11"    , testFlatDiff11      )
      , ("testFlatDiff12"    , testFlatDiff12      )
      , ("testFlatDiff13"    , testFlatDiff13      )
      , ("testFlatDiff14"    , testFlatDiff14      )
      , ("testFlatDiff15"    , testFlatDiff15      )
      , ("testFlatDiff16"    , testFlatDiff16      )
      , ("testFlatDiff17"    , testFlatDiff17      )
      , ("testFlatDiff18"    , testFlatDiff18      )
      , ("testFlatDiff19"    , testFlatDiff19      )
      , ("testFlatDiff20"    , testFlatDiff20      )
      , ("testFlatDiff21"    , testFlatDiff21      )
      , ("testFlatDiff23"    , testFlatDiff23      )
      , ("testFlatDiff24"    , testFlatDiff24      )
      , ("testMkNode00"      , testMkNode00        )
      , ("testMkNode01"      , testMkNode01        )
      , ("testMkNode02"      , testMkNode02        )
      , ("testMkNode03"      , testMkNode03        )
      , ("testMkNode04"      , testMkNode04        )
      , ("testMkNode05"      , testMkNode05        )
      , ("testUnion00"       , testUnion00         )
      , ("testUnion01"       , testUnion01         )
      , ("testUnion02"       , testUnion02         )
      , ("testUnion03"       , testUnion03         )
      , ("testUnion04"       , testUnion04         )
      , ("testUnion05"       , testUnion05         )
      , ("testUnion06"       , testUnion06         )
      , ("testUnion07"       , testUnion07         )
      , ("testPaths00"       , testPaths00         )
      ]

  (* ---------------------------------------------------------------- *)

end
