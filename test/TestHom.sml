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
    val x1 = node( 0, s0, one )
    val h0 = cons 1 s0 id
    val c0 = eval h0 x1
    val y0 = node( 1, s0, x1 )
  in
    assertTrue( c0 = y0 )
  end

  (* ---------------------------------------------------------------- *)

  fun testCons01 () =
  let
    val s0 = flatNode( 0, IntVector.fromList[0], one )
    val x1 = node( 0, s0, one )
    val h0 = cons 1 s0 id
    val c0 = eval h0 x1
    val c1 = eval h0 x1
  in
    assertTrue( c0 = c1 )
  end

  (* ---------------------------------------------------------------- *)

  fun testFlatCons00 () =
  let
    val s0 = flatNode( 0, IntVector.fromList[0], one )
    val h0 = flatCons 1 (IntVector.fromList[0]) id
    val c0 = eval h0 s0
    val o0 = flatNode( 1, IntVector.fromList[0], s0 )
  in
    assertTrue( c0 = o0 )
  end

  (* ---------------------------------------------------------------- *)

  fun suite () =
      Test.labelTests
      [ ("testId00"          , testId00        )
      , ("testId01"          , testId01        )
      , ("testCons00"        , testCons00      )
      , ("testCons01"        , testCons01      )
      , ("testFlatCons00"    , testFlatCons00  )
      ]

  (* ---------------------------------------------------------------- *)

end