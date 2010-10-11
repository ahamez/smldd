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
      , ("testNested00"      , testNested00    )
      , ("testNested01"      , testNested01    )
      ]

  (* ---------------------------------------------------------------- *)

end
