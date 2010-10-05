structure TestSDD =
struct

  (* ---------------------------------------------------------------- *)
  
  open SDD
  open SMLUnit.Assert
  structure Test = SMLUnit.Test

  (* ---------------------------------------------------------------- *)

  fun testTerminal00 () =
    assertTrue( zero <> one )

  fun testMkFlatNode00 () =
    assertTrue( flatNode( 0, IntVector.fromList [] , one  ) = zero )

  fun testMkFlatNode01 () =
    assertTrue( flatNode( 0, IntVector.fromList [0], zero ) = zero )

  fun testMkFlatNode02 () =
    assertTrue( flatNode( 0, IntVector.fromList [] , zero ) = zero )

  fun testFlatUnion00 () =
  let
    val s0 = flatNode( 0, IntVector.fromList[1,2,3], one )
    val s1 = flatNode( 0, IntVector.fromList[0,2,3], one )
    val u0 = union [s0,s1]
    val o0 = flatNode( 0, IntVector.fromList[0,1,2,3], one)
  in
    assertTrue( u0 = o0 )
  end

  fun testFlatUnion01 () =
  let
    val s0 = flatNode( 1, IntVector.fromList[1,2,3], one )
    val s1 = flatNode( 0, IntVector.fromList[0,2,3], one )
  in
    ( union [s0,s1] ; fail "Must fail" )
    handle x as _ => assertEqualExceptionName x IncompatibleSDD
  end

  fun testFlatUnion02 () =
  let
    val s0 = flatNode( 1, IntVector.fromList[1,2,3], one )
  in
    ( union [s0,one] ; fail "Must fail" )
    handle x as _ => assertEqualExceptionName x IncompatibleSDD
  end

  fun testFlatUnion03 () =
  let
    val s0 = flatNode( 0, IntVector.fromList[1,2,3], one )
    val u0 = union [s0,zero]
    val o0 = flatNode( 0, IntVector.fromList[1,2,3], one)
  in
    assertTrue( u0 = o0 )
  end

  fun testFlatUnion04 () =
  let
    val s0 = flatNode( 0, IntVector.fromList[1,2,3], one )
    val s1 = flatNode( 0, IntVector.fromList[0,2,3], one )
    val s2 = flatNode( 0, IntVector.fromList[0,666], one )
    val s3 = flatNode( 0, IntVector.fromList[42,43,44], one )
    val s4 = flatNode( 0, IntVector.fromList[0], one )
    val s5 = flatNode( 0, IntVector.fromList[~273,17,33], one )
    val u0 = union [s0,s1,s2,s3,s4,s5]
    val o0 = flatNode( 0
                     , IntVector.fromList[~273,0,1,2,3,17,33,42,43,44,666]
                     , one)
  in
    assertTrue( u0 = o0 )
  end

  fun testFlatUnion05 () =
  let
    val s0 = flatNode( 0, IntVector.fromList[1,2,3], one )
    val s1 = flatNode( 0, IntVector.fromList[0,2,3], one )
    val s2 = flatNode( 0, IntVector.fromList[0,666], one )
    val s3 = flatNode( 0, IntVector.fromList[42,43,44], one )
    val s4 = flatNode( 0, IntVector.fromList[0], one )
    val s5 = flatNode( 0, IntVector.fromList[~273,17,33], one )
  in
    ( union [s0,s1,s2,s3,s4,s5,one] ; fail "Must fail" )
    handle x as _ => assertEqualExceptionName x IncompatibleSDD
  end

  fun testFlatUnion06 () =
  let
    val s0 = flatNode( 0, IntVector.fromList[1,2,3], one )
    val s1 = flatNode( 0, IntVector.fromList[0,2,3], one )
    val s2 = flatNode( 1, IntVector.fromList[0], s0)
    val s3 = flatNode( 1, IntVector.fromList[0], s1)
    val u0 = union [s2,s3]
    val o0 = flatNode( 1, IntVector.fromList[0]
                     , flatNode( 0, IntVector.fromList[0,1,2,3], one )
                     )
  in
    assertTrue( u0 = o0 )
  end

  fun testFlatUnion07 () =
  let
    val s0 = flatNode( 0, IntVector.fromList[1,2,3], one )
    val u0 = union [s0,s0]
  in
    assertTrue( u0 = s0 )
  end

  fun testFlatInter00 () =
  let
    val s0 = flatNode( 0, IntVector.fromList[1,2,3], one )
    val s1 = flatNode( 0, IntVector.fromList[0,2,3], one )
    val i1 = intersection [s0,s1]
    val o0 = flatNode( 0, IntVector.fromList[2,3], one )
  in
    assertTrue( i1 = o0 )
  end

  fun testFlatInter01 () =
  let
    val s0 = flatNode( 0, IntVector.fromList[1,2,3], one )
    val i1 = intersection [s0,zero]
  in
    assertTrue( i1 = zero )
  end

  fun testFlatInter02 () =
  let
    val s0 = flatNode( 0, IntVector.fromList[1,2,3], one )
    val i1 = intersection [s0,s0]
  in
    assertTrue( i1 = s0 )
  end

  fun testFlatInter03 () =
  let
    val s0 = flatNode( 1, IntVector.fromList[1,2,3], one )
    val s1 = flatNode( 0, IntVector.fromList[0,2,3], one )
  in
    ( intersection [s0,s1] ; fail "Must fail" )
    handle x as _ => assertEqualExceptionName x IncompatibleSDD
  end

  fun testFlatInter04 () =
  let
    val s0 = flatNode( 42, IntVector.fromList[1,2,4], one )
  in
    ( intersection [one,s0] ; fail "Must fail" )
    handle x as _ => assertEqualExceptionName x IncompatibleSDD
  end

  fun testFlatInter05 () =
  let
    val s0 = flatNode( 42, IntVector.fromList[0,1,2,3], one )
    val s1 = flatNode( 42, IntVector.fromList[4,5,6,7], one )
    val i0 = intersection [s0, s1]
  in
    assertTrue( i0 = zero )
  end

  fun testFlatInter06 () =
  let
    val s0 = flatNode( 42, IntVector.fromList[0,1,2,3], one )
    val s1 = flatNode( 42, IntVector.fromList[4,5,6,7], one )
    val s2 = flatNode( 0, IntVector.fromList [0], s0 )
    val s3 = flatNode( 0, IntVector.fromList [0], s1 )
    val i0 = intersection [s2, s3]
  in
    assertTrue( i0 = zero )
  end

  fun testFlatDiff00 () =
  let
    val d0 = difference( one, one )
  in
    assertTrue( d0 = zero )
  end

  fun testFlatDiff01 () =
  let
    val s0 = flatNode( 0, IntVector.fromList[0,1,2,3], one )
    val s1 = flatNode( 0, IntVector.fromList[4,5,6,7], one )
    val d0 = difference( s1, s0 )
  in
    assertTrue( d0 = s1 )
  end

  fun testFlatDiff02 () =
  let
    val s0 = flatNode( 0, IntVector.fromList[0,1,2,3], one )
    val s1 = flatNode( 0, IntVector.fromList[4,5,6,7], one )
    val d0 = difference( s0, s1 )
  in
    assertTrue( d0 = s0 )
  end

  fun testFlatDiff03 () =
  let
    val s0 = flatNode( 0, IntVector.fromList[0,1,2,3], one )
    val s1 = flatNode( 0, IntVector.fromList[0,3], one )
    val d0 = difference( s0, s1 )
    val o0 = flatNode( 0, IntVector.fromList[1,2], one )
  in
    assertTrue( d0 = o0 )
  end

  fun testFlatDiff04 () =
  let
    val s0 = flatNode( 0, IntVector.fromList[0,1,2,3], one )
    val s1 = flatNode( 0, IntVector.fromList[0,3], one )
    val d0 = difference( s1, s0 )
    val _ = print ((toString d0) ^ "\n")
  in
    assertTrue( d0 = zero )
  end

  fun testFlatDiff05 () =
  let
    val s0 = flatNode( 0, IntVector.fromList[0,1,2,3], one )
    val s1 = flatNode( 0, IntVector.fromList[0,4], one )
    val d0 = difference( s1, s0 )
    val o0 = flatNode( 0, IntVector.fromList[4], one )
  in
    assertTrue( d0 = o0 )
  end

  (* ---------------------------------------------------------------- *)

  fun suite () =
      Test.labelTests
      [
        ("Terminals00"       , testTerminal00      )
      , ("MakeFlatNode00"    , testMkFlatNode00    )
      , ("MakeFlatNode01"    , testMkFlatNode01    )
      , ("MakeFlatNode02"    , testMkFlatNode02    )
      , ("FlatUnion00"       , testFlatUnion00     )
      , ("FlatUnion01"       , testFlatUnion01     )
      , ("FlatUnion02"       , testFlatUnion02     )
      , ("FlatUnion03"       , testFlatUnion03     )
      , ("FlatUnion04"       , testFlatUnion04     )
      , ("FlatUnion05"       , testFlatUnion05     )
      , ("FlatUnion06"       , testFlatUnion06     )
      , ("FlatUnion07"       , testFlatUnion07     )
      , ("FlatInter00"       , testFlatInter00     )
      , ("FlatInter01"       , testFlatInter01     )
      , ("FlatInter02"       , testFlatInter02     )
      , ("FlatInter03"       , testFlatInter03     )
      , ("FlatInter04"       , testFlatInter04     )
      , ("FlatInter05"       , testFlatInter05     )
      , ("FlatInter06"       , testFlatInter06     )
      , ("testFlatDiff00"    , testFlatDiff00      )
      , ("testFlatDiff01"    , testFlatDiff01      )
      , ("testFlatDiff02"    , testFlatDiff02      )
      , ("testFlatDiff03"    , testFlatDiff03      )
      , ("testFlatDiff04"    , testFlatDiff04      )
      , ("testFlatDiff05"    , testFlatDiff05      )
      ]

  (* ---------------------------------------------------------------- *)

end
