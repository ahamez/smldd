structure TestTools =
struct

open Tools
open SMLUnit.Assert
structure Test = SMLUnit.Test

val values = SDD.Values o IntVector.fromList

fun eqPaths ( [], [] ) = true
|   eqPaths ( [], _  ) = false
|   eqPaths ( _ , [] ) = false
|   eqPaths ( x::xs, y::ys ) =
let
  fun eqHelper ( [], [] ) = true
  |   eqHelper ( [], _  ) = false
  |   eqHelper ( _ , [] ) = false
  |   eqHelper ( (vr,vl)::xs', (vr',vl')::ys') =
            IntVariable.eq( vr, vr' )
    andalso DiscreteIntValues.eq( vl, vl' )
    andalso eqHelper( xs', ys' )
in
  eqHelper( x, y ) andalso eqPaths( xs, ys )
end

fun pathsToString [] = ""
|   pathsToString xs =
let

  fun pathToString [] = ""
  |   pathToString ((vr,vl)::path) =
    "(" ^ (IntVariable.toString vr) ^ "," 
  ^ (DiscreteIntValues.toString vl) ^ ") -> "
  ^ (pathToString path)

in
  String.concatWith "\n" (map pathToString xs)
end

fun testPaths00 () =
let
  val s0 = SDD.node( 0, values [1,2,3], SDD.one )
  val p0 = paths s0
  val o0 = [ [ ( 0, IntVector.fromList [1,2,3]) ] ]
in
  assertTrue( eqPaths( p0, o0 ) )
end

fun testPaths01 () =
let
  val s0 = SDD.node( 0, values [1,2,3], SDD.one )
  val s1 = SDD.node( 1, values [4,5,6], s0 )
  val p0 = paths s1
  val o0 = [ [ ( 1, IntVector.fromList [4,5,6])
             , ( 0, IntVector.fromList [1,2,3])
             ]
           ]
in
  assertTrue( eqPaths( p0, o0 ) )
end

fun testPaths02 () =
let
  val s0 = SDD.node( 0, values [0], SDD.one )
  val s1 = SDD.node( 1, values [0], s0 )
  val s2 = SDD.node( 0, values [1], SDD.one )
  val s3 = SDD.node( 1, values [1], s2 )
  val s4 = SDD.union [s1,s3]
  val p0 = paths s4
  val o0 = [ [ ( 1, IntVector.fromList [1])
             , ( 0, IntVector.fromList [1])
             ]
           , [ ( 1, IntVector.fromList [0])
             , ( 0, IntVector.fromList [0])
             ]
           ]
in
  assertTrue( eqPaths( p0, o0 ) )
end

fun testPaths03 () =
let
  val s0 = SDD.node( 0, values [1,2,3], SDD.one )
  val x0 = SDD.node( 0, SDD.Nested s0, SDD.one )
  val p0 = paths x0
  val o0 = [ [ ( 0, IntVector.fromList [1,2,3]) ] ]
in
  assertTrue( eqPaths( p0, o0 ) )
end

fun testPaths04 () =
let
  val s0 = SDD.node( 0, values [1,2,3], SDD.one )
  val x0 = SDD.node( 0, SDD.Nested s0, SDD.one )
  val x1 = SDD.node( 1, values [0], x0 )
  val p0 = paths x1
  val o0 = [ [ ( 1, IntVector.fromList [0])
             , ( 0, IntVector.fromList [1,2,3])
             ]
           ]
in
  assertTrue( eqPaths( p0, o0 ) )
end

fun testPaths05 () =
let
  val s0 = SDD.node( 0, values [1,2,3], SDD.one )
  val x0 = SDD.node( 0, SDD.Nested s0, SDD.one )
  val x1 = SDD.node( 1, SDD.Nested s0, x0 )
  val p0 = paths x1
  val o0 = [ [ ( 0, IntVector.fromList [1,2,3])
             , ( 0, IntVector.fromList [1,2,3])
             ]
           ]
in
  assertTrue( eqPaths( p0, o0 ) )
end

fun testPaths06 () =
let
  val s0 = SDD.node( 0, values [1,2,3], SDD.one )
  val x0 = SDD.node( 0, SDD.Nested s0, SDD.one )
  val s1 = SDD.node( 0, values [4,5,6], SDD.one )
  val x1 = SDD.node( 1, SDD.Nested s1, x0 )
  val p0 = paths x1
  val o0 = [ [ ( 0, IntVector.fromList [4,5,6])
             , ( 0, IntVector.fromList [1,2,3])
             ]
           ]
in
  assertTrue( eqPaths( p0, o0 ) )
end

fun testPaths07 () =
let
  val s0 = SDD.node( 0, values [1,2], SDD.one )
  val x0 = SDD.node( 0, SDD.Nested s0, SDD.one )
  val s1 = SDD.node( 0, values [3,4], SDD.one )
  val x1 = SDD.node( 1, SDD.Nested s1, x0 )

  val s2 = SDD.node( 0, values [5,6], SDD.one )
  val x2 = SDD.node( 0, SDD.Nested s2, SDD.one )
  val s3 = SDD.node( 0, values [7,8], SDD.one )
  val x3 = SDD.node( 1, SDD.Nested s3, x2 )

  val x4 = SDD.union [ x1, x3 ]

  val p0 = paths x4
  val o0 = [ [ ( 0, IntVector.fromList [7,8])
             , ( 0, IntVector.fromList [5,6])
             ]
           , [ ( 0, IntVector.fromList [3,4])
             , ( 0, IntVector.fromList [1,2])
             ]
           ]
in
  assertTrue( eqPaths( p0, o0 ) )
end

fun testPaths08 () =
let
  val s0 = SDD.node( 0, values [0], SDD.one )
  val s1 = SDD.node( 1, values [0], s0 )
  val s2 = SDD.node( 0, values [1], SDD.one )
  val s3 = SDD.node( 1, values [1], s2 )
  val s4 = SDD.union [ s1, s3 ]
  val s5 = SDD.node( 2, values [0], s4 )

  val s6 = SDD.node( 0, values [2], SDD.one )
  val s7 = SDD.node( 1, values [2], s6 )
  val s8 = SDD.node( 2, values [2], s7 )

  val s9 = SDD.union [ s5, s8 ]

  val p0 = paths s9
  val o0 = [ [ ( 2, IntVector.fromList [2]) 
             , ( 1, IntVector.fromList [2])
             , ( 0, IntVector.fromList [2])
             ]
           , [ ( 2, IntVector.fromList [0]) 
             , ( 1, IntVector.fromList [0])
             , ( 0, IntVector.fromList [0])
             ]
           , [ ( 2, IntVector.fromList [0]) 
             , ( 1, IntVector.fromList [1])
             , ( 0, IntVector.fromList [1])
             ]
           ]
in
  assertTrue( eqPaths( p0, o0 ) )
end

fun testOrderPaths00 () =
let
  val ord0 = IntOrder.flatOrder [0,1,2,3]
  val cst  = IntSortedVector.fromList [0]
  fun f _  = cst
  val s0   = IntOrder.SDD ord0 f
  val p0   = orderPaths ord0 s0
  val o0   = [ [ ( 0, cst ), ( 1, cst ), ( 2, cst ), ( 3, cst ) ] ]
in
  assertTrue( eqPaths( p0, o0 ) )
end

fun testOrderPaths01 () =
let
  val vars = [0,1,2,3,4]
  val ord0 = IntOrder.transform IntOrder.Anonymise
               (IntOrder.transform (IntOrder.MaxLeaves 3)
                 (IntOrder.flatOrder vars)
                )
  val cst  = IntSortedVector.fromList [0]
  fun f _  = cst
  val s0   = IntOrder.SDD ord0 f

  val p0   = orderPaths ord0 s0
  val o0   = [[ ( 0, cst ), ( 1, cst ), ( 2, cst ), ( 3, cst ), ( 4, cst ) ]]
in
  assertTrue( eqPaths( p0, o0 ) )
end

fun testOrderPaths02 () =
let
  val vars = [0,1,2,3]
  val ord0 = IntOrder.transform IntOrder.Anonymise
               (IntOrder.transform (IntOrder.MaxLeaves 3)
                 (IntOrder.flatOrder vars)
                )
  fun f x  = IntSortedVector.fromList [x+100]
  val s0   = IntOrder.SDD ord0 f
  val p0   = orderPaths ord0 s0
  val o0   = [ [ ( 0, f 0 ), ( 1, f 1 ), ( 2, f 2 ), ( 3, f 3 ) ] ]
in
  assertTrue( eqPaths( p0, o0 ) )
end

fun suite () =
    Test.labelTests
    [ ("testPaths00"          , testPaths00        )
    , ("testPaths01"          , testPaths01        )
    , ("testPaths02"          , testPaths02        )
    , ("testPaths03"          , testPaths03        )
    , ("testPaths04"          , testPaths04        )
    , ("testPaths05"          , testPaths05        )
    , ("testPaths06"          , testPaths06        )
    , ("testPaths07"          , testPaths07        )
    , ("testPaths08"          , testPaths08        )
    , ("testOrderPaths00"     , testOrderPaths00   )
    , ("testOrderPaths01"     , testOrderPaths01   )
    ]

end
