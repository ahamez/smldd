structure TestUtil =
struct

open Util
open SMLUnit.Assert
structure Test = SMLUnit.Test

fun testShuffle00 () =
let
  val l = List.tabulate (100, Util.id)
  val r = shuffle l
in
  assertTrue( l <> r )
end

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

fun suite () =
    Test.labelTests
    [ ("testShuffle00"          , testShuffle00        )
    , ("testIntInfToString00"   , testIntInfToString00 )
    , ("testIntInfToString01"   , testIntInfToString01 )
    , ("testIntInfToString02"   , testIntInfToString02 )
    , ("testIntInfToString03"   , testIntInfToString03 )
    , ("testIntInfToString04"   , testIntInfToString04 )
    , ("testIntInfToString05"   , testIntInfToString05 )
    , ("testIntInfToString06"   , testIntInfToString06 )
    , ("testIntInfToString07"   , testIntInfToString07 )
    , ("testIntInfToString08"   , testIntInfToString08 )
    , ("testIntInfToString09"   , testIntInfToString09 )
    ]

end
