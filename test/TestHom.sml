structure TestHom =
struct

  (* ---------------------------------------------------------------- *)
  
  open Hom
  open SDD
  open SMLUnit.Assert
  structure Test = SMLUnit.Test

  (* ---------------------------------------------------------------- *)

  val values = Values o IntVector.fromList

  (* ---------------------------------------------------------------- *)
  (* ---------------------------------------------------------------- *)

  fun pre c values =
    (*IntVector.map (fn x => x-c )
      (IntVector.fromList
        (List.filter (fn x => x >= c ) (IntVectorToList values)))*)
  IntVector.fromList
    (List.mapPartial (fn x => if x < c then
                                NONE
                              else
                                SOME (x-c)
                      )
                      (IntVectorToList values)
    )

  fun post c values =
    IntVector.map (fn x => x + c) values

  (* ---------------------------------------------------------------- *)
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

  fun testCons02 () =
  let
    val s0 = flatNode( 0, IntVector.fromList[0], one )
    val h0 = mkCons 0 (Values (IntVector.fromList [0])) id
    val c0 = eval h0 one
  in
    assertTrue( c0 = s0 )
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

  fun testFunction10 () =
  let
    fun f0 _ = IntVector.fromList []
    val s0 = node( 0, Values (IntVector.fromList[0,1,2,3]), one )
    val s1 = node( 1, Values (IntVector.fromList[0,1,2,3]), s0 )
    val h0 = mkFunction (ref f0) 1
    val s2 = eval h0 s1
  in
    assertTrue( s2 = zero )
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

  fun testNested02 () =
  let
    val f0 = IntVector.map (fn x => x+1)
    val h0 = mkFunction (ref f0) 0
    val h1 = mkNested h0 0
    val s0 = node( 0, Values (IntVector.fromList [0,1,2]), one )
    val x0 = node( 0, Nested s0, one )
    val x1 = eval h1 x0
    val o0 = node( 0, Values (IntVector.fromList [1,2,3]), one )
    val y0 = node( 0, Nested o0, one )

  in
    assertTrue( y0 = x1 )
  end

  (* ---------------------------------------------------------------- *)

  fun testNested03 () =
  let
    val f0 = IntVector.map (fn x => x+1)
    val h0 = mkFunction (ref f0) 0
    val h1 = mkNested h0 0
    val s0 = node( 0, Values (IntVector.fromList [0,1,2]), one )
    val x0 = node( 0, Nested s0, one )
    val x1 = node( 1, Nested s0, x0 )
    val x2 = eval h1 x1
    val o0 = node( 0, Values (IntVector.fromList [1,2,3]), one )
    val o1 = node( 0, Values (IntVector.fromList [0,1,2]), one )
    val y0 = node( 0, Nested o0, one )
    val y1 = node( 1, Nested o1, y0 )
  in
    assertTrue( y1 = x2 )
  end

  (* ---------------------------------------------------------------- *)

  fun testNested04 () =
  let
    fun f0 _ = IntVector.fromList []
    val h0 = mkFunction (ref f0) 0
    val h1 = mkNested h0 0
    val s0 = node( 0, Values (IntVector.fromList [0,1,2]), one )
    val x0 = node( 0, Nested s0, one )
    val x1 = node( 1, Nested s0, x0 )
    val x2 = eval h1 x1
  in
    assertTrue( x2 = zero )
  end

  (* ---------------------------------------------------------------- *)

  fun testNested05 () =
  let
    fun f0 _ = IntVector.fromList []
    val h0 = mkFunction (ref f0) 0
    val h1 = mkNested h0 1
    val s0 = node( 0, Values (IntVector.fromList [0,1,2]), one )
    val x0 = node( 0, Nested s0, one )
    val x1 = node( 1, Nested s0, x0 )
    val x2 = eval h1 x1
  in
    assertTrue( x2 = zero )
  end

  (* ---------------------------------------------------------------- *)

  fun testNested06 () =
  let
    fun f0 _ = IntVector.fromList []
    val h0 = mkFunction (ref f0) 0
    val h1 = mkNested h0 2
    val s0 = node( 0, Values (IntVector.fromList [0,1,2]), one )
    val x0 = node( 0, Nested s0, one )
    val x1 = node( 1, Nested s0, x0 )
    val x2 = eval h1 x1
  in
    assertTrue( x2 = x1 )
  end

  (* ---------------------------------------------------------------- *)

  fun testUnion00 () =
  let
    val h0 = mkUnion [id]
    val s0 = node( 0, Values (IntVector.fromList [0,1,2]), one)
    val s1 = eval h0 s0
  in
    assertTrue( s1 = s0 )
  end

  (* ---------------------------------------------------------------- *)

  fun testUnion01 () =
  let
    val h0 = mkUnion [id,id,id]
    val s0 = node( 0, Values (IntVector.fromList [0,1,2]), one)
    val s1 = eval h0 s0
  in
    assertTrue( s1 = s0 )
  end

  (* ---------------------------------------------------------------- *)

  fun testUnion02 () =
  let
    val f0 = IntVector.map (fn x => x+1)
    val f1 = IntVector.map (fn x => x+2)
    val h0 = mkUnion [ mkFunction (ref f0) 0, mkFunction (ref f1) 0]
    val s0 = node( 0, Values (IntVector.fromList [0,1]), one)
    val s1 = eval h0 s0
    val o0 = node( 0, Values (IntVector.fromList [1,2,3]), one )
  in
    assertTrue( s1 = o0 )
  end

  (* ---------------------------------------------------------------- *)

  fun testUnion03 () =
  let
    val f0 = IntVector.map (fn x => x+1)
    val f1 = IntVector.map (fn x => x+2)
    val h0 = mkUnion [ mkFunction (ref f0) 0, mkFunction (ref f1) 0, id ]
    val s0 = node( 0, Values (IntVector.fromList [0,1]), one)
    val s1 = eval h0 s0
    val o0 = node( 0, Values (IntVector.fromList [0,1,2,3]), one )
  in
    assertTrue( s1 = o0 )
  end

  (* ---------------------------------------------------------------- *)

  fun testUnion04 () =
  let
    val f0 = IntVector.map (fn x => x+1)
    val h0 = mkUnion [ mkFunction (ref f0) 0, mkFunction (ref f0) 0 ]
    val s0 = node( 0, Values (IntVector.fromList [0,1]), one)
    val s1 = eval h0 s0
    val o0 = node( 0, Values (IntVector.fromList [1,2]), one )
  in
    assertTrue( s1 = o0 )
  end

  (* ---------------------------------------------------------------- *)

  fun testUnion05 () =
  let
    val r0 = ref (IntVector.map (fn x => x+1))
    val h0 = mkUnion [ mkFunction r0 0, mkFunction r0 0 ]
    val s0 = node( 0, Values (IntVector.fromList [0,1]), one)
    val s1 = eval h0 s0
    val o0 = node( 0, Values (IntVector.fromList [1,2]), one )
  in
    assertTrue( s1 = o0 )
  end

  (* ---------------------------------------------------------------- *)

  fun testUnion06 () =
  let
    val S0  = node( 0, values [1],
              node( 1, values [2],
               node( 2, values [0],
                node( 3, values [0],
                 node( 4, values [0], one)))))

    val t1pre1  = mkFunction (ref (pre 1 )) 0
    val t1pre2  = mkFunction (ref (pre 2 )) 1
    val t1post1 = mkFunction (ref (post 1)) 2
    val t1post2 = mkFunction (ref (post 1)) 3
    val t1post3 = mkFunction (ref (post 1)) 4
    val t1     = mkComposition
                  (mkComposition t1post1 (mkComposition t1post2
                                           (mkComposition t1post3 id)))
                  (mkComposition t1pre1 (mkComposition t1pre2 id ))

    val t2pre1  = mkFunction (ref (pre 1 )) 3
    val t2post1 = mkFunction (ref (post 1)) 1
    val t2     = mkComposition
                  (mkComposition t2post1 id)
                  (mkComposition t2pre1  id)

    val t3pre1  = mkFunction (ref (pre 1 )) 4
    val t3post1 = mkFunction (ref (post 1)) 1
    val t3     = mkComposition
                  (mkComposition t3post1 id)
                  (mkComposition t3pre1  id)

    val t4pre1  = mkFunction (ref (pre 1 )) 2
    val t4post1 = mkFunction (ref (post 1)) 2
    val t4     = mkComposition
                  (mkComposition t4post1 id)
                  (mkComposition t4pre1  id)

    val t5pre1  = mkFunction (ref (pre 1 )) 2
    val t5post1 = mkFunction (ref (post 1)) 0
    val t5     = mkComposition
                  (mkComposition t5post1 id)
                  (mkComposition t5pre1  id)


    val h0 = mkUnion [id,t1,t2,t3,t4,t5]
    val s0 = eval h0 S0
    val h1 = mkUnion [t1,t2,t3,t4,t5,id]
    val s1 = eval h1 S0
    val h2 = mkUnion [t1,t3,t5,t2,t4,id]
    val s2 = eval h2 S0

  in
    assertTrue ( s0 = s1 andalso s0 = s2 )
  end

  (* ---------------------------------------------------------------- *)

  fun testFixpoint00 () =
  let
    val h0 = mkFixpoint id
    val s0 = node( 0, Values (IntVector.fromList [0,1]), one)
    val s1 = eval h0 s0
  in
    assertTrue( s0 = s1 )
  end

  (* ---------------------------------------------------------------- *)

  fun testFixpoint01 () =
  let
    val f0 = IntVector.map (fn x => if x < 4 then x + 1 else x)
    val h0 = mkFunction (ref f0) 0
    val h1 = mkUnion [h0,id]
    val h2 = mkFixpoint h1
    val s0 = node( 0, Values (IntVector.fromList [0,1]), one)
    val s1 = eval h2 s0
    val o0 = node( 0, Values (IntVector.fromList [0,1,2,3,4]), one )
  in
    assertTrue( o0 = s1 )
  end

  (* ---------------------------------------------------------------- *)

  fun testFixpoint02 () =
  let
    val f0 = IntVector.map (fn x => if x < 4 then x + 1 else x)
    val h0 = mkFunction (ref f0) 0
    val h2 = mkFixpoint h0
    val s0 = node( 0, Values (IntVector.fromList [0]), one)
    val s1 = eval h2 s0
    val o0 = node( 0, Values (IntVector.fromList [4]), one )
  in
    assertTrue( o0 = s1 )
  end

  (* ---------------------------------------------------------------- *)

  fun testFixpoint03 () =
  let
    val f0 = IntVector.map (fn x => if x < 4 then x + 1 else x)
    val h0 = mkFunction (ref f0) 0
    val h2 = mkFixpoint h0
    val s0 = node( 0, Values (IntVector.fromList [0,1,2]), one)
    val s1 = eval h2 s0
    val o0 = node( 0, Values (IntVector.fromList [4]), one )
  in
    assertTrue( o0 = s1 )
  end

  (* ---------------------------------------------------------------- *)

  fun testFixpoint04 () =
  let
    val s0 = node( 0, Values(IntVector.fromList [1]),
              node( 1, Values(IntVector.fromList [0]), one))

    val t1pre  = mkFunction (ref (pre 1 )) 0
    val t1post = mkFunction (ref (post 1)) 1
    val t1     = mkComposition
                  (mkComposition t1post id)
                  (mkComposition t1pre id )

    val t2pre  = mkFunction (ref (pre 1 )) 1
    val t2post = mkFunction (ref (post 1)) 0
    val t2     = mkComposition
                  (mkComposition t2post id)
                  (mkComposition t2pre id )

    val h = mkFixpoint (mkUnion [id,t1,t2])
    val s = eval h s0

    val o0 = node( 0, Values(IntVector.fromList [1]),
              node( 1, Values(IntVector.fromList [0]), one))
    val o1 = node( 0, Values(IntVector.fromList [0]),
              node( 1, Values(IntVector.fromList [1]), one))
    val o2 = union [o0,o1]
  in
    assertTrue (o2 = s)
  end

  (* ---------------------------------------------------------------- *)

  fun testFixpoint05 () =
  let
    val s0 = node( 0, values [1],
              node( 1, values [2],
               node( 2, values [0],
                node( 3, values [0],
                 node( 4, values [0], one)))))

    val t1pre1  = mkFunction (ref (pre 1 )) 0
    val t1pre2  = mkFunction (ref (pre 2 )) 1
    val t1post1 = mkFunction (ref (post 1)) 2
    val t1post2 = mkFunction (ref (post 1)) 3
    val t1post3 = mkFunction (ref (post 1)) 4
    val t1     = mkComposition
                  (mkComposition t1post1 (mkComposition t1post2
                                           (mkComposition t1post3 id)))
                  (mkComposition t1pre1 (mkComposition t1pre2 id ))

    val t2pre1  = mkFunction (ref (pre 1 )) 3
    val t2post1 = mkFunction (ref (post 1)) 1
    val t2     = mkComposition
                  (mkComposition t2post1 id)
                  (mkComposition t2pre1  id)

    val t3pre1  = mkFunction (ref (pre 1 )) 4
    val t3post1 = mkFunction (ref (post 1)) 1
    val t3     = mkComposition
                  (mkComposition t3post1 id)
                  (mkComposition t3pre1  id)

    val t4pre1  = mkFunction (ref (pre 1 )) 2
    val t4post1 = mkFunction (ref (post 1)) 2
    val t4     = mkComposition
                  (mkComposition t4post1 id)
                  (mkComposition t4pre1  id)

    val t5pre1  = mkFunction (ref (pre 1 )) 2
    val t5post1 = mkFunction (ref (post 1)) 0
    val t5     = mkComposition
                  (mkComposition t5post1 id)
                  (mkComposition t5pre1  id)


    val h = mkFixpoint (mkUnion [t3,t2,t1,t4,t5,id])
    (*val h = mkFixpoint (mkUnion [t1,t2,t3,t4,t5,id])*)
    val s = eval h s0

    val o0 = node( 0, values [1],
              node( 1, values [2],
               node( 2, values [0],
                node( 3, values [0],
                 node( 4, values [0], one)))))
    val o1 = node( 0, values [0],
              node( 1, values [0],
               node( 2, values [1],
                node( 3, values [1],
                 node( 4, values [1], one)))))
    val o2 = node( 0, values [0],
              node( 1, values [1],
               node( 2, values [1],
                node( 3, values [0],
                 node( 4, values [1], one)))))
    val o3 = node( 0, values [0],
              node( 1, values [1],
               node( 2, values [1],
                node( 3, values [1],
                 node( 4, values [0], one)))))
    val o4 = node( 0, values [1],
              node( 1, values [0],
               node( 2, values [0],
                node( 3, values [1],
                 node( 4, values [1], one)))))
    val o5 = node( 0, values [0],
              node( 1, values [2],
               node( 2, values [1],
                node( 3, values [0],
                 node( 4, values [0], one)))))
    val o6 = node( 0, values [1],
              node( 1, values [1],
               node( 2, values [0],
                node( 3, values [0],
                 node( 4, values [1], one)))))
    val o7 = node( 0, values [1],
              node( 1, values [1],
               node( 2, values [0],
                node( 3, values [1],
                 node( 4, values [0], one)))))

    val o8 = union [o0,o1,o2,o3,o4,o5,o6,o7]
  in
    assertTrue (o8 = s)
  end

  (* ---------------------------------------------------------------- *)

  fun suite () =
      Test.labelTests
      [ ("testId00"          , testId00        )
      , ("testId01"          , testId01        )
      , ("testCons00"        , testCons00      )
      , ("testCons01"        , testCons01      )
      , ("testCons02"        , testCons02      )
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
      , ("testFunction10"    , testFunction10  )
      , ("testNested00"      , testNested00    )
      , ("testNested01"      , testNested01    )
      , ("testNested02"      , testNested02    )
      , ("testNested03"      , testNested03    )
      , ("testNested04"      , testNested04    )
      , ("testNested05"      , testNested05    )
      , ("testNested06"      , testNested06    )
      , ("testUnion00"       , testUnion00     )
      , ("testUnion01"       , testUnion01     )
      , ("testUnion02"       , testUnion02     )
      , ("testUnion03"       , testUnion03     )
      , ("testUnion04"       , testUnion04     )
      , ("testUnion05"       , testUnion05     )
      , ("testUnion06"       , testUnion06     )
      , ("testFixpoint00"    , testFixpoint00  )
      , ("testFixpoint01"    , testFixpoint01  )
      , ("testFixpoint02"    , testFixpoint02  )
      , ("testFixpoint03"    , testFixpoint03  )
      , ("testFixpoint04"    , testFixpoint04  )
      , ("testFixpoint05"    , testFixpoint05  )
      ]

  (* ---------------------------------------------------------------- *)

end
