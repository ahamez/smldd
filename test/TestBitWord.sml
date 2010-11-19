structure TestBitWord =
struct

open BitWord
open SMLUnit.Assert
structure Test = SMLUnit.Test

fun testEmpty00 () =
  assertTrue( mkEmpty() = Word32.fromInt 0 )

fun testEmpty01 () =
  assertTrue( empty (mkEmpty()) )

fun testInsert00 () =
let
  val e = mkEmpty()
  val x = insert e 10
in
  assertTrue( x = Word32.fromInt 1024 )
end

fun testInsert01 () =
let
  val e = mkEmpty()
in
  (insert e 100 ; fail "Must fail")
  handle x => assertEqualExceptionName x Domain
end

fun testInsert02 () =
let
  val e = mkEmpty()
  val x = insert e 10
  val y = insert x 3
in
  assertTrue( y = Word32.fromInt (1024 + 8) )
end

fun testLength00 () =
let
  val e = mkEmpty ()
  val x = insert e 10
  val y = insert x 3
in
  assertTrue( length y = 2 )
end

fun testUnion00 () =
let
  val e = mkEmpty ()
  val x = insert e 10
  val y = insert e 3
  val z = insert (insert e 10) 3
in
  assertTrue( union (x,y) = z )
end

fun testUnion01 () =
let
  val e = mkEmpty ()
  val x = insert e 10
in
  assertTrue( union (x,x) = x )
end

fun testInter00 () =
let
  val e = mkEmpty ()
  val x = insert e 10
in
  assertTrue( intersection (x,e) = e )
end

fun testInter01 () =
let
  val e = mkEmpty ()
  val x = insert e 10
  val y = insert e 3
in
  assertTrue( intersection (x,y) = e )
end

fun testInter02 () =
let
  val e = mkEmpty ()
  val x = insert e 10
  val y = insert (insert e 10) 3
in
  assertTrue( intersection (x,y) = x )
end

fun testDiff00 () =
let
  val e = mkEmpty ()
  val x = insert e 10
  val y = insert (insert e 10) 3
in
  assertTrue( difference (x,y) = e )
end

fun testDiff01 () =
let
  val e = mkEmpty ()
  val x = insert e 10
  val y = insert (insert e 10) 3
  val z = insert e 3
in
  assertTrue( difference (y,x) = z )
end

fun suite () =
    Test.labelTests
    [ ("testEmpty00"            , testEmpty00         )
    , ("testEmpty01"            , testEmpty01         )
    , ("testInsert00"           , testInsert00        )
    , ("testInsert01"           , testInsert01        )
    , ("testInsert02"           , testInsert02        )
    , ("testLength00"           , testLength00        )
    , ("testUnion00"            , testUnion00         )
    , ("testUnion01"            , testUnion01         )
    , ("testInter00"            , testInter00         )
    , ("testInter01"            , testInter01         )
    , ("testInter02"            , testInter02         )
    , ("testDiff00"             , testDiff00          )
    , ("testDiff01"             , testDiff01          )
    ]

end
