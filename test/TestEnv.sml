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
fun f0 c (FuncValues (cxt,values)) =
  FuncValuesRes ( cxt, SV.map (fn x => x + c) values )
|   f0 _ Print =
  PrintRes "f0"
|   f0 _ Hash =
  HashRes (Hash.hashInt 123)

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
fun testMergeContexts00() =
let
  val cxt0 = addValues emptyContext 0 (SV.fromList [0,1])
  val cxt1 = addValues emptyContext 1 (SV.fromList [3,4])
  val cxt2 = mergeContexts [cxt0,cxt1]
  val cxt3 = addValues emptyContext 0 (SV.fromList [0,1])
  val cxt4 = addValues cxt3 1 (SV.fromList [3,4])
in
  assertTrue( eqContext( cxt4, cxt2 ) )
end

(*--------------------------------------------------------------------------*)
fun testMergeContexts01() =
let
  val cxt0 = addValues emptyContext 0 (SV.fromList [0,1])
  val cxt1 = addValues emptyContext 1 (SV.fromList [3,4])
  val cxt2 = mergeContexts [cxt1,cxt0]
  val cxt3 = addValues emptyContext 0 (SV.fromList [0,1])
  val cxt4 = addValues cxt3 1 (SV.fromList [3,4])
in
  assertTrue( eqContext( cxt4, cxt2 ) )
end

(*--------------------------------------------------------------------------*)
fun testMergeContexts02() =
let
  val cxt0 = addValues emptyContext 0 (SV.fromList [0,1])
  val cxt1 = addValues emptyContext 1 (SV.fromList [3,4])
  val cxt2 = addValues emptyContext 1 (SV.fromList [4,5])
  val cxt3 = mergeContexts [cxt1,cxt0,cxt2]
  val cxt4 = addValues emptyContext 0 (SV.fromList [0,1])
  val cxt5 = addValues cxt4 1 (SV.fromList [3,4,5])
in
  assertTrue( eqContext( cxt3, cxt5 ) )
end

(*--------------------------------------------------------------------------*)
fun testMergeContexts03() =
let
  val cxt0 = addValues emptyContext 0 (SV.fromList [0,1])
  val cxt1 = addValues emptyContext 1 (SV.fromList [3,4])
  val cxt2 = addValues emptyContext 9 (SV.fromList [4,5])
  val cxt3 = mergeContexts [cxt2,cxt0,cxt1]
  val cxt4 = addValues emptyContext 0 (SV.fromList [0,1])
  val cxt5 = addValues cxt4 1 (SV.fromList [3,4])
  val cxt6 = addValues cxt5 9 (SV.fromList [4,5])
in
  assertTrue( eqContext( cxt3, cxt6 ) )
end

(*--------------------------------------------------------------------------*)
fun testMergeContexts04() =
let
  val cxt0 = addValues emptyContext 0 (SV.fromList [0,1])
  val cxt1 = addValues emptyContext 1 (SV.fromList [3,4])
  val cxt2 = addValues emptyContext 9 (SV.fromList [4,5])
  val cxt3 = mergeContexts [cxt0,cxt1,cxt2]
  val cxt4 = addValues emptyContext 0 (SV.fromList [0,1])
  val cxt5 = addValues cxt4 1 (SV.fromList [3,4])
  val cxt6 = addValues cxt5 9 (SV.fromList [4,5])
in
  assertTrue( eqContext( cxt3, cxt6 ) )
end

(*--------------------------------------------------------------------------*)
fun testIntersectContexts00() =
let
  val cxt0 = addValues emptyContext 0 (SV.fromList [0,1])
  val cxt1 = addValues emptyContext 1 (SV.fromList [3,4])
  val cxt2 = intersectContexts [cxt0,cxt1]
in
  assertTrue( isEmptyContext cxt2 )
end

(*--------------------------------------------------------------------------*)
fun testIntersectContexts01() =
let
  val cxt0 = addValues emptyContext 0 (SV.fromList [0,1])
  val cxt1 = addValues emptyContext 0 (SV.fromList [3,4])
  val cxt2 = intersectContexts [cxt0,cxt1]
in
  assertTrue( isEmptyContext cxt2 )
end

(*--------------------------------------------------------------------------*)
fun testIntersectContexts02() =
let
  val cxt0 = addValues emptyContext 0 (SV.fromList [0,1])
  val cxt1 = addValues emptyContext 1 (SV.fromList [3,4])
  val cxt2 = addValues emptyContext 9 (SV.fromList [4,5])
  val cxt3 = intersectContexts [cxt0,cxt1,cxt2]
in
  assertTrue( isEmptyContext cxt3 )
end

(*--------------------------------------------------------------------------*)
fun testIntersectContexts03() =
let
  val cxt0 = addValues emptyContext 0 (SV.fromList [0,1])
  val cxt1 = addValues emptyContext 0 (SV.fromList [1,2])
  val cxt3 = intersectContexts [cxt0,cxt1]
  val cxt4 = addValues emptyContext 0 (SV.fromList [1])
in
  assertTrue( eqContext( cxt4, cxt3 ) )
end

(*--------------------------------------------------------------------------*)
fun testIntersectContexts04() =
let
  val cxt0 = addValues emptyContext 0 (SV.fromList [0,1])
  val cxt1 = addValues emptyContext 1 (SV.fromList [2,3])
  val cxt2 = addValues emptyContext 2 (SV.fromList [4,5])
  val cxt3 = mergeContexts [cxt0,cxt2,cxt1]

  val cxt4 = addValues emptyContext 0 (SV.fromList [0,1])
  val cxt5 = addValues emptyContext 1 (SV.fromList [2,3])
  val cxt6 = addValues emptyContext 3 (SV.fromList [6,7])
  val cxt7 = mergeContexts [cxt5,cxt6,cxt4]

  val cxtx = intersectContexts [cxt3,cxt7]

  val cxt8 = addValues emptyContext 1 (SV.fromList [2,3])
  val cxt9 = addValues cxt8 0 (SV.fromList [0,1])

in
  assertTrue( eqContext( cxt9, cxtx ) )
end

(*--------------------------------------------------------------------------*)
fun testIntersectContexts05() =
let
  val cxt0 = addValues emptyContext 0 (SV.fromList [0,1])
  val cxt1 = addValues emptyContext 1 (SV.fromList [2,3])
  val cxt2 = addValues emptyContext 2 (SV.fromList [4,5])
  val cxt3 = mergeContexts [cxt0,cxt2,cxt1]

  val cxt4 = addValues emptyContext 0 (SV.fromList [0,1])
  val cxt5 = addValues emptyContext 1 (SV.fromList [2,3])
  val cxt6 = addValues emptyContext 2 (SV.fromList [4,5])
  val cxt7 = mergeContexts [cxt5,cxt6,cxt4]

  val cxtx = intersectContexts [cxt3,cxt7]
in
  assertTrue( eqContext( cxt7, cxtx ) )
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
    [ ("testEmptyContext00"       , testEmptyContext00       )
    , ("testAddValues00"          , testAddValues00          )
    , ("testAddValues01"          , testAddValues01          )
    , ("testAddValues02"          , testAddValues02          )
    , ("testRemoveVariable00"     , testRemoveVariable00     )
    , ("testRemoveVariable01"     , testRemoveVariable01     )
    , ("testMergeContexts00"      , testMergeContexts00      )
    , ("testMergeContexts01"      , testMergeContexts01      )
    , ("testMergeContexts02"      , testMergeContexts02      )
    , ("testMergeContexts03"      , testMergeContexts03      )
    , ("testMergeContexts04"      , testMergeContexts04      )
    , ("testIntersectContexts00"  , testIntersectContexts00  )
    , ("testIntersectContexts01"  , testIntersectContexts01  )
    , ("testIntersectContexts02"  , testIntersectContexts02  )
    , ("testIntersectContexts03"  , testIntersectContexts03  )
    , ("testIntersectContexts04"  , testIntersectContexts04  )
    , ("testIntersectContexts05"  , testIntersectContexts05  )
    , ("testContextContent00"     , testContextContent00     )
    ]

(*--------------------------------------------------------------------------*)

end
