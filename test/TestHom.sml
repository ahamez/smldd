structure TestHom =
struct

  (* ---------------------------------------------------------------- *)
  
  open SMLDD
  open SMLDD.Hom
  open SMLDD.SDD
  open SMLUnit.Assert
  structure SV = IntSortedVector
  structure Test = SMLUnit.Test

  (* ---------------------------------------------------------------- *)

  val values = Values o SV.fromList

  (* ---------------------------------------------------------------- *)
  (* Some functions used by mkFunction *)
  (* ---------------------------------------------------------------- *)
  fun pre c (Eval values) =
    EvalRes (SV.mapPartial (fn x => if x < c then NONE else SOME (x-c))
                           values
            )
  |   pre _ Selector = SelectorRes true
  |   pre c Print    = PrintRes ("Pre" ^ (Int.toString c))
  |   pre c Hash =
    HashRes ( Hash.hashCombine( Hash.hashInt c, Hash.hashInt 4956317) )

  (* ---------------------------------------------------------------- *)
  fun preTest c (Eval values) =
    EvalRes (SV.mapPartial  (fn x => if x < c then SOME x else NONE) values )
  |   preTest c Print = PrintRes ("Pre" ^ (Int.toString c))
  |   preTest _ Selector = SelectorRes true
  |   preTest c Hash =
    HashRes ( Hash.hashCombine( Hash.hashInt c, Hash.hashInt 4956317) )

  (* ---------------------------------------------------------------- *)
  fun post c (Eval values) =
    EvalRes (SV.map (fn x => x + c) values)
  |   post c Print = PrintRes ("Post" ^ (Int.toString c))
  |   post c Hash =
    HashRes ( Hash.hashCombine( Hash.hashInt c, Hash.hashInt 1481673) )

  (* ---------------------------------------------------------------- *)
  fun f0 c (Eval values) =
    EvalRes (SV.map (fn x => x + c) values)
  |   f0 _ Print =
    PrintRes "f0"
  |   f0 _ Hash =
    HashRes (Hash.hashInt 123)

  (* ---------------------------------------------------------------- *)
  fun f1 (Eval values) =
    EvalRes (SV.mapPartial (fn x => if x > 2 then SOME x else NONE )
                           values
            )
  |   f1 Print =
    PrintRes "f1"
  |   f1 Hash =
    HashRes (Hash.hashInt 456)

  (* ---------------------------------------------------------------- *)
  fun f2 (Eval _) =
    EvalRes (SV.fromList [])
  |   f2 Print =
    PrintRes "f2"
  |   f2 Hash =
    HashRes (Hash.hashInt 789)

  (* ---------------------------------------------------------------- *)
  fun f3 (Eval _) =
    EvalRes (SV.fromList [1,2,3])
  |   f3 Print =
    PrintRes "f3"
  |   f3 Hash =
    HashRes (Hash.hashInt 987)

  (* ---------------------------------------------------------------- *)
  fun f4 (Eval values) =
    EvalRes (SV.map (fn x => x) values)
  |   f4 Print =
    PrintRes "f4"
  |   f4 Hash =
    HashRes (Hash.hashInt 654)

  (* ---------------------------------------------------------------- *)
  fun f5 (Eval values) =
    EvalRes (SV.map (fn x => if x < 4 then x + 1 else x) values)
  |   f5 Print =
    PrintRes "f5"
  |   f5 Hash =
    HashRes (Hash.hashInt 321)

  (* ---------------------------------------------------------------- *)
  fun f6 (Eval values) =
    EvalRes (SV.map (fn x => x) values)
  |   f6 Hash =
    HashRes (Hash.hashInt 654)
  |   f6 Selector =
    SelectorRes true

  (* ---------------------------------------------------------------- *)
  (* ---------------------------------------------------------------- *)

  (* ---------------------------------------------------------------- *)
  fun testId00 () =
    assertTrue( eval id one = one )

  (* ---------------------------------------------------------------- *)
  fun testId01 () =
  let
    val s0 = node( 0, values [0,1], one )
  in
    assertTrue( eval id s0 = s0 )
  end

  (* ---------------------------------------------------------------- *)
  fun testCons00 () =
  let
    val s0 = node( 0, values [0], one )
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
    val s0 = node( 0, values [0], one )
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
    val s0 = node( 0, values[0], one )
    val h0 = mkCons 0 (values [0]) id
    val c0 = eval h0 one
  in
    assertTrue( c0 = s0 )
  end

  (* ---------------------------------------------------------------- *)

  fun testFunction00 () =
  let
    val s0 = node( 0, values[0,1,2,3], one )
    val h0 = mkFunction (ref (f0 1)) 0
    val s1 = eval h0 s0
    val o0 = node( 0, values[1,2,3,4], one )
  in
    assertTrue( s1 = o0 )
  end

  (* ---------------------------------------------------------------- *)

  fun testFunction01 () =
  let
    val h0 = mkFunction (ref (f0 0)) 0
    val s0 = eval h0 SDD.zero
  in
    assertTrue( s0 = SDD.zero )
  end

  (* ---------------------------------------------------------------- *)

  fun testFunction02 () =
  let
    val s0 = node( 0, values[0,1,2,3], one )
    val h0 = mkFunction (ref (f0 1)) 1
    val s1 = eval h0 s0
  in
    assertTrue( s1 = s0 )
  end

  (* ---------------------------------------------------------------- *)

  fun testFunction03 () =
  let
    val s0 = node( 0, values[0,1,2,3,4], one )
    val h0 = mkFunction (ref f1) 0
    val s1 = eval h0 s0
    val o0 = node( 0, values[3,4], one )
  in
    assertTrue( s1 = o0 )
  end

  (* ---------------------------------------------------------------- *)

  fun testFunction04 () =
  let
    val s0   = node( 0, values[0,1,2,3], one )
    val h0   = mkFunction (ref f2) 0
    val s1   = eval h0 s0
  in
    assertTrue( s1 = SDD.zero )
  end

  (* ---------------------------------------------------------------- *)

  fun testFunction05 () =
  let
    val s0   = node( 0, values[0], one )
    val s1   = node( 1, values[0], s0  )
    val s2   = node( 0, values[1], one )
    val s3   = node( 1, values[1], s2  )
    val s4   = union [s3,s1]
    val h0   = mkFunction (ref f3) 0
    val s5   = eval h0 s4
    val o0   = node( 0, values[1,2,3], one )
    val o1   = node( 1, values[0,1]  , o0  )
  in
    assertTrue( s5 = o1 )
  end

  (* ---------------------------------------------------------------- *)

  fun testFunction06 () =
  let
    val s0 = node( 0, values[0,1,2,3], one )
    val s1 = node( 1, values[0,1,2,3], s0 )
    val h0 = mkFunction (ref (f0 1)) 0
    val s2 = eval h0 s1
    val o0 = node( 0, values[1,2,3,4], one )
    val o1 = node( 1, values[0,1,2,3], o0 )
  in
    assertTrue( s2 = o1 )
  end

  (* ---------------------------------------------------------------- *)

  fun testFunction07 () =
  let
    val s0   = node( 0, (values[0,1,2,3]), one )
    val s1   = node( 1, (values[0,1,2,3]), s0 )
    val h0   = mkFunction (ref f2) 0
    val s2   = eval h0 s1
  in
    assertTrue( s2 = zero )
  end

  (* ---------------------------------------------------------------- *)

  fun testFunction08 () =
  let
    val s0 = node( 0, (values[0,1,2,3]), one )
    val x0 = node( 0, Nested s0, one )
    val h0 = mkFunction (ref f4) 0
  in
    ( eval h0 x0 ; fail "Must fail" )
    handle x => assertEqualExceptionName x FunctionHomOnNested
  end

  (* ---------------------------------------------------------------- *)

  fun testFunction09 () =
  let
    val x0 = node( 0, Nested one, one )
    val h0 = mkFunction (ref f4) 0
  in
    ( eval h0 x0 ; fail "Must fail" )
    handle x => assertEqualExceptionName x FunctionHomOnNested
  end

  (* ---------------------------------------------------------------- *)

  fun testFunction10 () =
  let
    val s0   = node( 0, (values[0,1,2,3]), one )
    val s1   = node( 1, (values[0,1,2,3]), s0 )
    val h0   = mkFunction (ref f2) 1
    val s2   = eval h0 s1
  in
    assertTrue( s2 = zero )
  end

  (* ---------------------------------------------------------------- *)

  fun testFunction11 () =
  let
    val x0 = node( 0, Nested one, one )
    val h0 = mkFunction (ref f6) 0
  in
    ( eval h0 x0 ; fail "Must fail" )
    handle x => assertEqualExceptionName x FunctionHomOnNested
  end


  (* ---------------------------------------------------------------- *)

  fun testNested00 () =
  let
    val s0 = node( 0, (values[0]), one)
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
    val h0 = mkFunction (ref (f0 1)) 0
    val h1 = mkNested h0 0
    val s0 = node( 0, (values [0,1,2]), one )
    val x0 = node( 0, Nested s0, one )
    val x1 = eval h1 x0
    val o0 = node( 0, (values [1,2,3]), one )
    val y0 = node( 0, Nested o0, one )

  in
    assertTrue( y0 = x1 )
  end

  (* ---------------------------------------------------------------- *)

  fun testNested03 () =
  let
    val h0 = mkFunction (ref (f0 1)) 0
    val h1 = mkNested h0 0
    val s0 = node( 0, (values [0,1,2]), one )
    val x0 = node( 0, Nested s0, one )
    val x1 = node( 1, Nested s0, x0 )
    val x2 = eval h1 x1
    val o0 = node( 0, (values [1,2,3]), one )
    val o1 = node( 0, (values [0,1,2]), one )
    val y0 = node( 0, Nested o0, one )
    val y1 = node( 1, Nested o1, y0 )
  in
    assertTrue( y1 = x2 )
  end

  (* ---------------------------------------------------------------- *)

  fun testNested04 () =
  let
    val h0   = mkFunction (ref f2) 0
    val h1   = mkNested h0 0
    val s0   = node( 0, (values [0,1,2]), one )
    val x0   = node( 0, Nested s0, one )
    val x1   = node( 1, Nested s0, x0 )
    val x2   = eval h1 x1
  in
    assertTrue( x2 = zero )
  end

  (* ---------------------------------------------------------------- *)

  fun testNested05 () =
  let
    val h0   = mkFunction (ref f2) 0
    val h1   = mkNested h0 1
    val s0   = node( 0, (values [0,1,2]), one )
    val x0   = node( 0, Nested s0, one )
    val x1   = node( 1, Nested s0, x0 )
    val x2   = eval h1 x1
  in
    assertTrue( x2 = zero )
  end

  (* ---------------------------------------------------------------- *)

  fun testNested06 () =
  let
    val h0   = mkFunction (ref f2) 0
    val h1   = mkNested h0 2
    val s0   = node( 0, (values [0,1,2]), one )
    val x0   = node( 0, Nested s0, one )
    val x1   = node( 1, Nested s0, x0 )
    val x2   = eval h1 x1
  in
    assertTrue( x2 = x1 )
  end

  (* ---------------------------------------------------------------- *)

  fun testUnion00 () =
  let
    val h0 = mkUnion [id]
    val s0 = node( 0, (values [0,1,2]), one)
    val s1 = eval h0 s0
  in
    assertTrue( s1 = s0 )
  end

  (* ---------------------------------------------------------------- *)

  fun testUnion01 () =
  let
    val h0 = mkUnion [id,id,id]
    val s0 = node( 0, (values [0,1,2]), one)
    val s1 = eval h0 s0
  in
    assertTrue( s1 = s0 )
  end

  (* ---------------------------------------------------------------- *)

  fun testUnion02 () =
  let
    val h0 = mkUnion [ mkFunction (ref (f0 1)) 0, mkFunction (ref (f0 2)) 0]
    val s0 = node( 0, (values [0,1]), one)
    val s1 = eval h0 s0
    val o0 = node( 0, (values [1,2,3]), one )
  in
    assertTrue( s1 = o0 )
  end

  (* ---------------------------------------------------------------- *)

  fun testUnion03 () =
  let
    val h0 = mkUnion [ mkFunction (ref (f0 1)) 0, mkFunction (ref (f0 2)) 0
                     , id
                     ]
    val s0 = node( 0, (values [0,1]), one)
    val s1 = eval h0 s0
    val o0 = node( 0, (values [0,1,2,3]), one )
  in
    assertTrue( s1 = o0 )
  end

  (* ---------------------------------------------------------------- *)

  fun testUnion04 () =
  let
    val h0 = mkUnion [ mkFunction (ref (f0 1)) 0, mkFunction (ref (f0 1)) 0 ]
    val s0 = node( 0, (values [0,1]), one)
    val s1 = eval h0 s0
    val o0 = node( 0, (values [1,2]), one )
  in
    assertTrue( s1 = o0 )
  end

  (* ---------------------------------------------------------------- *)

  fun testUnion05 () =
  let
    val r0 = ref (f0 1)
    val h0 = mkUnion [ mkFunction r0 0, mkFunction r0 0 ]
    val s0 = node( 0, (values [0,1]), one)
    val s1 = eval h0 s0
    val o0 = node( 0, (values [1,2]), one )
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
    val s0 = node( 0, (values [0,1]), one)
    val s1 = eval h0 s0
  in
    assertTrue( s0 = s1 )
  end

  (* ---------------------------------------------------------------- *)

  fun testFixpoint01 () =
  let
    val h0 = mkFunction (ref f5) 0
    val h1 = mkUnion [h0,id]
    val h2 = mkFixpoint h1
    val s0 = node( 0, (values [0,1]), one)
    val s1 = eval h2 s0
    val o0 = node( 0, (values [0,1,2,3,4]), one )
  in
    assertTrue( o0 = s1 )
  end

  (* ---------------------------------------------------------------- *)

  fun testFixpoint02 () =
  let
    val h0 = mkFunction (ref f5) 0
    val h2 = mkFixpoint h0
    val s0 = node( 0, (values [0]), one)
    val s1 = eval h2 s0
    val o0 = node( 0, (values [4]), one )
  in
    assertTrue( o0 = s1 )
  end

  (* ---------------------------------------------------------------- *)

  fun testFixpoint03 () =
  let
    val h0 = mkFunction (ref f5) 0
    val h2 = mkFixpoint h0
    val s0 = node( 0, values [0,1,2], one)
    val s1 = eval h2 s0
    val o0 = node( 0, values [4], one )
  in
    assertTrue( o0 = s1 )
  end

  (* ---------------------------------------------------------------- *)

  fun testFixpoint04 () =
  let
    val s0 = node( 0, values [1],
              node( 1, values [0], one))

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

    val o0 = node( 0, values [1],
              node( 1, values [0], one))
    val o1 = node( 0, values [0],
              node( 1, values [1], one))
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

(*--------------------------------------------------------------------------*)
(* Get philosophers' state space *)
fun testFixpoint06 () =
let

  fun SDDFromList xs =
  let
    fun loop _ []      = one
    |   loop i (x::xs) = node( i, values [x], loop (i+1) xs )
  in
    loop 0 xs
  end

  fun mkComp []      = raise Empty
  |   mkComp [x]     = x
  |   mkComp (x::xs) = mkComposition x (mkComp xs)

                      (*0 1 2 3 4 5 6 7 8 9*)
  val s0 = SDDFromList [0,1,0,0,1,0,1,0,0,1]

  val post1 = ref (post 1)
  val pre1  = ref (pre 1)

  val P0TakeLeft1 = mkComp [ mkFunction post1 2
                           , mkFunction pre1 4
                           , mkFunction pre1 1
                           ]
  val P0TakeRight1 = mkComp [ mkFunction post1 3
                            , mkFunction pre1 4
                            , mkFunction pre1 6
                            ]
  val P0TakeRight2 = mkComp [ mkFunction post1 0
                            , mkFunction pre1 2
                            , mkFunction pre1 6
                            ]
  val P0TakeLeft2 = mkComp [ mkFunction post1 0
                           , mkFunction pre1 3
                           , mkFunction pre1 1
                           ]
  val P0GoThink = mkComp [ mkFunction post1 4
                         , mkFunction post1 1
                         , mkFunction post1 6
                         , mkFunction pre1 0
                         ]
  val P1TakeLeft1 = mkComp [ mkFunction post1 7
                           , mkFunction pre1 9
                           , mkFunction pre1 6
                           ]
  val P1TakeRight1 = mkComp [ mkFunction post1 8
                            , mkFunction pre1 9
                            , mkFunction pre1 1
                            ]
  val P1TakeRight2 = mkComp [ mkFunction post1 5
                            , mkFunction pre1 7
                            , mkFunction pre1 1
                            ]
  val P1TakeLeft2 = mkComp [ mkFunction post1 5
                           , mkFunction pre1 8
                           , mkFunction pre1 6
                           ]
  val P1GoThink = mkComp [ mkFunction post1 9
                         , mkFunction post1 6
                         , mkFunction post1 1
                         , mkFunction pre1 5
                         ]

  val h = mkFixpoint(
              mkUnion [ P0TakeLeft1, P0TakeRight1, P0TakeRight2
                      , P0TakeLeft2, P0GoThink
                      , P1TakeLeft1, P1TakeRight1, P1TakeRight2
                      , P1TakeLeft2, P1GoThink
                      , id
                      ]
                    )

  (*val homDot = Tools.homToDot h
  val homDotFile = TextIO.openOut "testFixpoint06.dot"
  val _ = TextIO.outputSubstr ( homDotFile
                              , Substring.extract(homDot,0, NONE))*)

  val s = eval h s0

  val p1 = SDDFromList [1,0,0,0,0,0,0,0,0,1]
  val p2 = SDDFromList [0,1,0,1,0,0,0,0,0,1]
  val p3 = SDDFromList [0,1,0,0,1,0,1,0,0,1]
  val p4 = SDDFromList [0,1,0,0,1,0,0,1,0,0]
  val p5 = SDDFromList [0,0,1,0,0,0,1,0,0,1]
  val p6 = SDDFromList [0,0,1,0,0,0,0,1,0,0]
  val p7 = SDDFromList [0,0,0,0,1,1,0,0,0,0]
  val p8 = SDDFromList [0,0,0,0,1,0,1,0,1,0]
  val p9 = SDDFromList [0,0,0,1,0,0,0,0,1,0]
  val o0 = union [p1,p2,p3,p4,p5,p6,p7,p8,p9]

in
  assertTrue( s = o0 )
end

(*--------------------------------------------------------------------------*)
(* Get dead states of philosophers *)
fun testIntersection00 () =
let

  fun SDDFromList xs =
  let
    fun loop _ []      = one
    |   loop i (x::xs) = node( i, values [x], loop (i+1) xs )
  in
    loop 0 xs
  end

                      (*0 1 2 3 4 5 6 7 8 9*)
  val p1 = SDDFromList [1,0,0,0,0,0,0,0,0,1]
  val p2 = SDDFromList [0,1,0,1,0,0,0,0,0,1]
  val p3 = SDDFromList [0,1,0,0,1,0,1,0,0,1]
  val p4 = SDDFromList [0,1,0,0,1,0,0,1,0,0]
  val p5 = SDDFromList [0,0,1,0,0,0,1,0,0,1]
  val p6 = SDDFromList [0,0,1,0,0,0,0,1,0,0]
  val p7 = SDDFromList [0,0,0,0,1,1,0,0,0,0]
  val p8 = SDDFromList [0,0,0,0,1,0,1,0,1,0]
  val p9 = SDDFromList [0,0,0,1,0,0,0,0,1,0]
  val s0 = union [p1,p2,p3,p4,p5,p6,p7,p8,p9]

  val P0TakeLeft1 = mkUnion [ mkFunction (ref (preTest 1)) 4
                            , mkFunction (ref (preTest 1)) 1
                            ]
  val P0TakeRight1 = mkUnion [ mkFunction (ref (preTest 1)) 4
                             , mkFunction (ref (preTest 1)) 6
                             ]
  val P0TakeRight2 = mkUnion [ mkFunction (ref (preTest 1)) 2
                             , mkFunction (ref (preTest 1)) 6
                             ]
  val P0TakeLeft2 = mkUnion [ mkFunction (ref (preTest 1)) 3
                            , mkFunction (ref (preTest 1)) 1
                            ]
  val P0GoThink = mkFunction (ref (preTest 1)) 0
  val P1TakeLeft1 = mkUnion [ mkFunction (ref (preTest 1)) 9
                            , mkFunction (ref (preTest 1)) 6
                            ]
  val P1TakeRight1 = mkUnion [ mkFunction (ref (preTest 1)) 9
                             , mkFunction (ref (preTest 1)) 1
                             ]
  val P1TakeRight2 = mkUnion [ mkFunction (ref (preTest 1)) 7
                             , mkFunction (ref (preTest 1)) 1
                             ]
  val P1TakeLeft2 = mkUnion [ mkFunction (ref (preTest 1)) 8
                            , mkFunction (ref (preTest 1)) 6
                            ]
  val P1GoThink = mkFunction (ref (preTest 1)) 5

  val hDead = mkIntersection [ P0TakeLeft1, P0TakeRight1, P0TakeRight2
                             , P0TakeLeft2, P0GoThink
                             , P1TakeLeft1, P1TakeRight1, P1TakeRight2
                             , P1TakeLeft2, P1GoThink
                             ]
  val dead = eval hDead s0

  val o1 = SDDFromList [0,0,1,0,0,0,0,1,0,0]
  val o2 = SDDFromList [0,0,0,1,0,0,0,0,1,0]
  val odead = union [o1,o2]

in
  assertTrue( dead = odead )
end

(*--------------------------------------------------------------------------*)
fun testFactorization00 () =
let
  fun f c (Eval values) =
    EvalRes (SV.map (fn x => x + c) values)
  |   f c Print =
    PrintRes ("f" ^ (Int.toString c))
  |   f c Hash =
    HashRes (Hash.hashInt c)

  val a = mkFunction (ref (f 0)) 0
  val b = mkFunction (ref (f 1)) 0
  val c = mkFunction (ref (f 2)) 0
  val d = mkFunction (ref (f 3)) 0

  val s0 = SDD.node( 0, SDD.Values (SV.fromList [0]), SDD.one )

  val o0 = SDD.union [ eval a (eval b (eval c (eval d s0)))
                     , eval a (eval b (eval c s0))
                     , eval a (eval b s0)
                     ]

  val habcd = mkComposition a (mkComposition b (mkComposition c d))
  val habc  = mkComposition a (mkComposition b c)
  val hab   = mkComposition a b

  val h = mkUnion [ habcd, habc, hab ]
  val s = eval h s0

  val homDot = Tools.homToDot h
  val homDotFile = TextIO.openOut "testFactorization00.dot"
  val _ = TextIO.outputSubstr ( homDotFile
                              , Substring.extract(homDot,0, NONE))

in
  assertTrue( s = o0 )
end

(*--------------------------------------------------------------------------*)
fun testFactorization01 () =
let
  fun f c (Eval values) =
    EvalRes (SV.map (fn x => x + c) values)
  |   f c Print =
    PrintRes ("f" ^ (Int.toString c))
  |   f c Hash =
    HashRes (Hash.hashInt c)

  val a = mkFunction (ref (f 0)) 0
  val b = mkFunction (ref (f 1)) 0
  val c = mkFunction (ref (f 2)) 0
  val d = mkFunction (ref (f 3)) 0

  val s0 = SDD.node( 0, SDD.Values (SV.fromList [0]), SDD.one )

  val o0 = SDD.union [ eval a (eval b (eval c (eval d s0)))
                     , eval a (eval b (eval c s0))
                     , eval a (eval b s0)
                     , eval a s0
                     ]

  val habcd = mkComposition a (mkComposition b (mkComposition c d))
  val habc  = mkComposition a (mkComposition b c)
  val hab   = mkComposition a b

  val h = mkUnion [ habcd, habc, hab, a ]
  val s = eval h s0

  val homDot = Tools.homToDot h
  val homDotFile = TextIO.openOut "testFactorization01.dot"
  val _ = TextIO.outputSubstr ( homDotFile
                              , Substring.extract(homDot,0, NONE))

in
  assertTrue( s = o0 )
end


(*--------------------------------------------------------------------------*)

  fun suite () =
      Test.labelTests
      [ ("testId00"            , testId00            )
      , ("testId01"            , testId01            )
      , ("testCons00"          , testCons00          )
      , ("testCons01"          , testCons01          )
      , ("testCons02"          , testCons02          )
      , ("testFunction00"      , testFunction00      )
      , ("testFunction01"      , testFunction01      )
      , ("testFunction02"      , testFunction02      )
      , ("testFunction03"      , testFunction03      )
      , ("testFunction04"      , testFunction04      )
      , ("testFunction05"      , testFunction05      )
      , ("testFunction06"      , testFunction06      )
      , ("testFunction07"      , testFunction07      )
      , ("testFunction08"      , testFunction08      )
      , ("testFunction09"      , testFunction09      )
      , ("testFunction10"      , testFunction10      )
      , ("testFunction11"      , testFunction11      )
      , ("testNested00"        , testNested00        )
      , ("testNested01"        , testNested01        )
      , ("testNested02"        , testNested02        )
      , ("testNested03"        , testNested03        )
      , ("testNested04"        , testNested04        )
      , ("testNested05"        , testNested05        )
      , ("testNested06"        , testNested06        )
      , ("testUnion00"         , testUnion00         )
      , ("testUnion01"         , testUnion01         )
      , ("testUnion02"         , testUnion02         )
      , ("testUnion03"         , testUnion03         )
      , ("testUnion04"         , testUnion04         )
      , ("testUnion05"         , testUnion05         )
      , ("testUnion06"         , testUnion06         )
      , ("testFixpoint00"      , testFixpoint00      )
      , ("testFixpoint01"      , testFixpoint01      )
      , ("testFixpoint02"      , testFixpoint02      )
      , ("testFixpoint03"      , testFixpoint03      )
      , ("testFixpoint04"      , testFixpoint04      )
      , ("testFixpoint05"      , testFixpoint05      )
      , ("testFixpoint06"      , testFixpoint06      )
      , ("testIntersection00"  , testIntersection00  )
      , ("testFactorization00" , testFactorization00 )
      , ("testFactorization01" , testFactorization01 )
      ]

  (* ---------------------------------------------------------------- *)

end
