structure TestEnv =
struct

(*--------------------------------------------------------------------------*)
open SMLDD
open SMLDD.Hom
open SMLDD.SDD
open SMLUnit.Assert
structure SV = IntSortedVector
structure Test = SMLUnit.Test

(*--------------------------------------------------------------------------*)
val values = Values o SV.fromList


(*--------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------*)




(*--------------------------------------------------------------------------*)
fun testEmptyContext00 () =
  assertTrue( isEmptyContext emptyContext )

(*--------------------------------------------------------------------------*)
fun testAddValues00 () =
let
  val cxt0 = addValues emptyContext 0 (SV.fromList [0,1])
  val cxt1 = addValues cxt0 0 (SV.fromList [3,4])
  val cxt2 = addValues emptyContext 0 (SV.fromList [0,1,3,4])
in
  assertTrue( eqContext(cxt1, cxt2 ) )
end

(*--------------------------------------------------------------------------*)
fun testAddValues01 () =
let
  val cxt0 = addValues emptyContext 0 (SV.fromList [0,1])
  val cxt1 = addValues cxt0 0 (SV.fromList [3,4])
  val cxt2 = addValues emptyContext 0 (SV.fromList [3,4])
  val cxt3 = addValues cxt2 0 (SV.fromList [0,1])
in
  assertTrue( eqContext(cxt1, cxt3 ) )
end

(*--------------------------------------------------------------------------*)
fun testAddValues02 () =
let
  val cxt0 = addValues emptyContext 0 (SV.fromList [0,1])
  val cxt1 = addValues cxt0 1 (SV.fromList [3,4])
  val cxt2 = addValues emptyContext 1 (SV.fromList [3,4])
  val cxt3 = addValues cxt2 0 (SV.fromList [0,1])
in
  assertTrue( eqContext(cxt1, cxt3 ) )
end

(*--------------------------------------------------------------------------*)
fun testRemoveVariable00 () =
let
  val cxt0 = addValues emptyContext 0 (SV.fromList [0,1])
  val cxt1 = addValues cxt0 1 (SV.fromList [3,4])
  val cxt2 = removeVariable cxt1 1
in
  assertTrue( eqContext(cxt2, cxt0 ) )
end

(*--------------------------------------------------------------------------*)
fun testRemoveVariable01 () =
let
  val cxt0 = addValues emptyContext 0 (SV.fromList [0,1])
  val cxt1 = addValues cxt0 1 (SV.fromList [3,4])
  val cxt2 = removeVariable cxt1 0
  val cxt3 = addValues emptyContext 1 (SV.fromList [3,4])
in
  assertTrue( eqContext(cxt2, cxt3 ) )
end

(*--------------------------------------------------------------------------*)
fun testContextContent00 () =
let
  val s = SDD.fromList [(0,values [0]),(1,values [0]),(2,values [3])]
in
  print (toString s)
end

(*--------------------------------------------------------------------------*)

(*--------------------------------------------------------------------------*)

fun suite () =
    Test.labelTests
    [ ("testEmptyContext00"     , testEmptyContext00    )
    , ("testAddValues00"        , testAddValues00       )
    , ("testAddValues01"        , testAddValues01       )
    , ("testAddValues02"        , testAddValues02       )
    , ("testRemoveVariable00"   , testRemoveVariable00  )
    , ("testRemoveVariable01"   , testRemoveVariable01  )
    , ("testContextContent00"   , testContextContent00  )
    ]

(*--------------------------------------------------------------------------*)

end
