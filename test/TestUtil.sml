structure TestUtil =
struct

open Util
open SMLUnit.Assert
structure Test = SMLUnit.Test

fun testIntInfToString00 () =
let
  val x = IntInf.fromInt 0
  val s = IntInfToString x (SOME 0) (SOME 2)
in
  assertTrue( s = "0.00E0" )
end

fun testIntInfToString01 () =
let
  val x = IntInf.fromInt 101
  val s = IntInfToString x (SOME 0) (SOME 2)
in
  assertTrue( s = "1.01E2" )
end

fun testIntInfToString02 () =
let
  val x = IntInf.fromInt 101
  val s = IntInfToString x NONE (SOME 2)
in
  assertTrue( s = "101" )
end

fun testIntInfToString03 () =
let
  val x = IntInf.fromInt 101
  val s = IntInfToString x (SOME 0) (SOME 5)
in
  assertTrue( s = "1.01000E2" )
end

fun testIntInfToString04 () =
let
  val x = IntInf.fromInt 1001
  val s = IntInfToString x (SOME 0) (SOME 2)
in
  assertTrue( s = "1.00E3" )
end


fun testIntInfToString05 () =
let
  val x = IntInf.fromInt 1005
  val s = IntInfToString x (SOME 0) (SOME 2)
in
  assertTrue( s = "1.00E3" )
end

fun testIntInfToString06 () =
let
  val x = IntInf.fromInt 1008
  val s = IntInfToString x (SOME 0) (SOME 2)
in
  assertTrue( s = "1.01E3" )
end

fun testIntInfToString07 () =
let
  val x = IntInf.fromInt 1108
  val s = IntInfToString x (SOME 0) (SOME 2)
in
  assertTrue( s = "1.11E3" )
end

fun testIntInfToString08 () =
let
  val x = IntInf.fromInt 1998
  val s = IntInfToString x (SOME 0) (SOME 2)
in
  assertTrue( s = "2.00E3" )
end

fun testIntInfToString09 () =
let
  val str = String.concat [ "265613988875874769338781322035779626829233"
                          , "4526533944959745749617390924909013021829943"
                          , "84699044001"]
  val x = valOf( IntInf.fromString str )
  val s = IntInfToString x (SOME 0) (SOME 2)
in
  assertTrue( s = "2.66E95" )
end

fun testIntInfToString10 () =
let
  val str = String.concat [ "265613988875874769338781322035779626829233"
                          , "4526533944959745749617390924909013021829943"
                          , "84699044001"]
  val x = valOf( IntInf.fromString str )
  val s = IntInfToString x (SOME 0) NONE
in
  assertTrue( s = "2.66E95" )
end

fun testTake00 () =
  assertTrue( take([],0) = [] )

fun testTake01 () =
  assertTrue( take([1,2,3],0) = [] )

fun testTake02 () =
  assertTrue( take([1,2,3],3) = [1,2,3] )

fun testTake03 () =
  assertTrue( take([1,2,3],100) = [1,2,3] )

fun testTake04 () =
  ( take( [1,2,3], ~3 ) ; fail "Must fail" )
  handle x => assertEqualExceptionName x Subscript

fun testVectorToList00 () =
  assertTrue( VectorToList (Vector.fromList [1,2]) = [1,2] )

fun suite () =
    Test.labelTests
    [ ("testIntInfToString00"   , testIntInfToString00 )
    , ("testIntInfToString01"   , testIntInfToString01 )
    , ("testIntInfToString02"   , testIntInfToString02 )
    , ("testIntInfToString03"   , testIntInfToString03 )
    , ("testIntInfToString04"   , testIntInfToString04 )
    , ("testIntInfToString05"   , testIntInfToString05 )
    , ("testIntInfToString06"   , testIntInfToString06 )
    , ("testIntInfToString07"   , testIntInfToString07 )
    , ("testIntInfToString08"   , testIntInfToString08 )
    , ("testIntInfToString09"   , testIntInfToString09 )
    , ("testIntInfToString10"   , testIntInfToString10 )
    , ("testTake00"             , testTake00           )
    , ("testTake01"             , testTake01           )
    , ("testTake02"             , testTake02           )
    , ("testTake03"             , testTake03           )
    , ("testTake04"             , testTake04           )
    ]

end
