structure TestHom =
struct

  (* ---------------------------------------------------------------- *)
  
  open Hom
  open SDD
  open SMLUnit.Assert
  structure Test = SMLUnit.Test

  (* ---------------------------------------------------------------- *)
  
  fun testId00 () =
    assertTrue( eval id one = one )

  (* ---------------------------------------------------------------- *)

  fun testId01 () =
  let
    val s0 = flatNode( 0, IntVector.fromList[0,1], one )
  in
    assertTrue( eval id s0 = s0 )
  end

  (* ---------------------------------------------------------------- *)

  fun testCons00 () =
  let
    val s0 = flatNode( 0, IntVector.fromList[0], one )
    val x1 = node( 0, Nested s0, one )
    val h0 = mkCons 1 (Nested s0) id
    val c0 = eval h0 x1
    val y0 = node( 1, Nested s0, x1 )
  in
    assertTrue( c0 = y0 )
  end

  (* ---------------------------------------------------------------- *)

  fun testCons01 () =
  let
    val s0 = flatNode( 0, IntVector.fromList[0], one )
    val x1 = node( 0, Nested s0, one )
    val h0 = mkCons 1 (Nested s0) id
    val c0 = eval h0 x1
    val c1 = eval h0 x1
  in
    assertTrue( c0 = c1 )
  end

  (* ---------------------------------------------------------------- *)

  fun testFunction00 () =
  let
    val s0 = node( 0, Values (IntVector.fromList[0,1,2,3]), one )
    val f0 = ref (IntVector.map (fn x => x + 1))
    val h0 = mkFunction f0 0
    val s1 = eval h0 s0
    val o0 = node( 0, Values (IntVector.fromList[1,2,3,4]), one )
  in
    assertTrue( s1 = o0 )
  end

  (* ---------------------------------------------------------------- *)

  fun testFunction01 () =
  let
    val f0 = ref (IntVector.map (fn x => x + 1))
    val h0 = mkFunction f0 0
    val s0 = eval h0 SDD.zero
  in
    assertTrue( s0 = SDD.zero )
  end

  (* ---------------------------------------------------------------- *)

  fun testFunction02 () =
  let
    val s0 = node( 0, Values (IntVector.fromList[0,1,2,3]), one )
    val f0 = ref (IntVector.map (fn x => x + 1))
    val h0 = mkFunction f0 1
    val s1 = eval h0 s0
  in
    assertTrue( s1 = s0 )
  end

  (* ---------------------------------------------------------------- *)

  fun testFunction03 () =
  let

    fun f0 xs = IntVector.fromList
                 (List.mapPartial (fn x => if x > 2 then
                                             SOME x
                                           else
                                             NONE
                                  )
                                  (IntVectorToList xs)
                 )

    val s0 = node( 0, Values (IntVector.fromList[0,1,2,3,4]), one )
    val h0 = mkFunction (ref f0) 0
    val s1 = eval h0 s0
    val o0 = node( 0, Values (IntVector.fromList[3,4]), one )
  in
    assertTrue( s1 = o0 )
  end

  (* ---------------------------------------------------------------- *)

  fun testFunction04 () =
  let
    fun f0 _ = IntVector.fromList []
    val s0 = node( 0, Values (IntVector.fromList[0,1,2,3]), one )
    val h0 = mkFunction (ref f0) 0
    val s1 = eval h0 s0
  in
    assertTrue( s1 = SDD.zero )
  end

  (* ---------------------------------------------------------------- *)

  fun testFunction05 () =
  let
    fun f0 _ = IntVector.fromList [1,2,3]
    val s0 = node( 0, Values (IntVector.fromList[0]), one )
    val s1 = node( 1, Values (IntVector.fromList[0]), s0  )
    val s2 = node( 0, Values (IntVector.fromList[1]), one )
    val s3 = node( 1, Values (IntVector.fromList[1]), s2  )
    val s4 = union [s3,s1]
    val h0 = mkFunction (ref f0) 0
    val s5 = eval h0 s4
    val o0 = node( 0, Values (IntVector.fromList[1,2,3]), one )
    val o1 = node( 1, Values (IntVector.fromList[0,1])  , o0  )
  in
    assertTrue( s5 = o1 )
  end

  (* ---------------------------------------------------------------- *)

  fun testFunction06 () =
  let
    val f0 = IntVector.map (fn x => x+1)
    val s0 = node( 0, Values (IntVector.fromList[0,1,2,3]), one )
    val s1 = node( 1, Values (IntVector.fromList[0,1,2,3]), s0 )
    val h0 = mkFunction (ref f0) 0
    val s2 = eval h0 s1
    val o0 = node( 0, Values (IntVector.fromList[1,2,3,4]), one )
    val o1 = node( 1, Values (IntVector.fromList[0,1,2,3]), o0 )
  in
    assertTrue( s2 = o1 )
  end

  (* ---------------------------------------------------------------- *)

  fun testFunction07 () =
  let
    fun f0 _ = IntVector.fromList []
    val s0 = node( 0, Values (IntVector.fromList[0,1,2,3]), one )
    val s1 = node( 1, Values (IntVector.fromList[0,1,2,3]), s0 )
    val h0 = mkFunction (ref f0) 0
    val s2 = eval h0 s1
  in
    assertTrue( s2 = zero )
  end

  (* ---------------------------------------------------------------- *)

  fun testFunction08 () =
  let
    fun f0 x = x
    val s0 = node( 0, Values (IntVector.fromList[0,1,2,3]), one )
    val x0 = node( 0, Nested s0, one )
    val h0 = mkFunction (ref f0) 0
  in
    ( eval h0 x0 ; fail "Must fail" )
    handle x as _ => assertEqualExceptionName x FunctionHomOnNested
  end

  (* ---------------------------------------------------------------- *)

  fun testFunction09 () =
  let
    fun f0 x = x
    val x0 = node( 0, Nested one, one )
    val h0 = mkFunction (ref f0) 0
  in
    ( eval h0 x0 ; fail "Must fail" )
    handle x as _ => assertEqualExceptionName x FunctionHomOnNested
  end

  (* ---------------------------------------------------------------- *)

  fun testNested00 () =
  let
    val s0 = node( 0, Values (IntVector.fromList[0]), one)
    val x0 = node( 0, Nested s0, one )
    val h0 = mkNested id 0
    val r0 = eval h0 x0
  in
    assertTrue( r0 = x0 )
  end

  (* ---------------------------------------------------------------- *)

  fun testNested01 () =
  let
    val h0 = mkNested id 0
  in
    assertTrue( h0 = id )
  end

  (* ---------------------------------------------------------------- *)

  fun suite () =
      Test.labelTests
      [ ("testId00"          , testId00        )
      , ("testId01"          , testId01        )
      , ("testCons00"        , testCons00      )
      , ("testCons01"        , testCons01      )
      , ("testFunction00"    , testFunction00  )
      , ("testFunction01"    , testFunction01  )
      , ("testFunction02"    , testFunction02  )
      , ("testFunction03"    , testFunction03  )
      , ("testFunction04"    , testFunction04  )
      , ("testFunction05"    , testFunction05  )
      , ("testFunction06"    , testFunction06  )
      , ("testFunction07"    , testFunction07  )
      , ("testFunction08"    , testFunction08  )
      , ("testFunction09"    , testFunction09  )
      , ("testNested00"      , testNested00    )
      , ("testNested01"      , testNested01    )
      ]

  (* ---------------------------------------------------------------- *)

end
