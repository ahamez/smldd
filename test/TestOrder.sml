structure TestOrder =
struct

  open SMLUnit.Assert
  open SMLDD
  structure Test = SMLUnit.Test
  structure SV = IntSortedVector
  open SMLDD.Order

  (* ---------------------------------------------------------------- *)
  fun f3 (Hom.FuncValues (cxt,_)) =
    Hom.FuncValuesRes ( cxt, SV.fromList [1,2,3] )
  |   f3 Hom.Print =
    Hom.PrintRes "f3"
  |   f3 Hom.Hash =
    Hom.HashRes (Hash.hashInt 987)

  fun testFlatOrder00 () =
  let
    val vars = ["a","b","c","d"]
    val _  = flatOrder vars
  in
    assertTrue( true )
  end

  fun testHierOrder00 () =
  let
    val ord0  = flatOrder ["a","b","c","d"]
    val ord1  = flatOrder ["d","e","f","g"]
    val ord2  = addHierarchicalNode (mkOrder()) "x" ord0
    val _  = addHierarchicalNode ord2 "y" ord1
  in
    assertTrue( true )
  end

  fun testMaxLeaves00 () =
  let
    val vars = ["a","b","c","d","e","f","g","h","i","j","k","l","m","n","o"]
    val ord  = flatOrder vars
    val _ = transform (MaxLeaves 5) ord
  in
    assertTrue( true )
  end

  fun testMaxLeaves01 () =
  let
    val vars = ["a","b","c","d","e","f","g","h","i","j","k","l","m","n"]
    val ord  = flatOrder vars
    val _ = transform (MaxLeaves 3) ord
  in
    assertTrue( true )
  end

  fun testMaxLeaves02 () =
  let
    val vars = ["a"]
    val ord  = flatOrder vars
  in
    (transform (MaxLeaves 0) ord ; fail "Must fail")
    handle x => assertEqualExceptionName x Domain
  end

  fun testMaxLeaves03 () =
  let
    val vars = ["a"]
    val ord  = flatOrder vars
  in
    (transform (MaxLeaves 1) ord ; fail "Must fail")
    handle x => assertEqualExceptionName x Domain
  end

  fun testFlatten00 () =
  let
    val vars  = ["a","b","c","d","e","f","g","h","i","j","k","l","m","n"]
    val ord   = flatOrder vars
    val ord'  = transform (MaxLeaves 3) ord
    val ord'' = transform Flatten ord'
  in
    assertTrue( eq( ord'', ord ) )
  end

  fun testSDD00 () =
  let
    val ord = flatOrder ["a","b","c","d"]
    val cst = IntSortedVector.fromList [0]
    val vst = SDD.Values cst
    fun f _ = cst
    val s0  = SDD ord f
    val o0  = SDD.fromList [(3,vst),(2,vst),(1,vst),(0,vst)]
  in
    assertTrue( SDD.eq(s0,o0) )
  end

  fun testSDD01 () =
  let
    val ord = flatOrder ["a","b","c","d"]
    val ord'  = transform (MaxLeaves 3) ord
    val cst = IntSortedVector.fromList [0]
    val vst = SDD.Values cst
    fun f _ = cst
    val s0  = SDD ord' f
    val o0  = SDD.node( 0
                      , SDD.Nested (SDD.fromList [(2,vst),(1,vst),(0,vst)])
                      , SDD.one
                      )
    val o1  = SDD.node( 1, SDD.Nested (SDD.node(3,vst,SDD.one)), o0 )
  in
    assertTrue( SDD.eq(s0,o1) )
  end

  fun testAnonymise00 () =
  let
    val ord  = flatOrder ["a","b","c","d"]
    val ord' = transform Anonymise (transform (MaxLeaves 3) ord)
    val cst  = IntSortedVector.fromList [0]
    val vst  = SDD.Values cst
    fun f _  = cst
    val s0   = SDD ord' f
    val o0   = SDD.node( 0
                       , SDD.Nested (SDD.fromList [(2,vst),(1,vst),(0,vst)])
                       , SDD.one
                       )
    val o1   = SDD.node( 1, SDD.Nested (SDD.node(0,vst,SDD.one)), o0 )
  in
    assertTrue( SDD.eq(o1,s0) )
  end

  fun testHom00 () =
  let
    val rf0  = ref f3
    val vars = ["a","b","c","d","e","f","g","h","i","j","k","l","m","n"]
    val ord  = flatOrder vars
    val h0   = hom ord "i" (fn v => Hom.mkFunction rf0 v)
    val o0   = Hom.mkFunction rf0 5
  in
    assertTrue( Hom.eq(h0,o0) )
  end

  fun testHom01 () =
  let
    val rf0  = ref f3
    val vars = ["a","b","c","d"]
    val ord  = transform (MaxLeaves 3) (flatOrder vars)
    val h0   = hom ord "c" (fn v => Hom.mkFunction rf0 v)
    val o0   = Hom.mkNested (Hom.mkFunction rf0 1) 0
  in
    assertTrue( Hom.eq(h0,o0) )
  end

  fun testHom02 () =
  let
    val rf0  = ref f3
    val vars = []
    val ord  = transform (MaxLeaves 3) (flatOrder vars)
    val h0   = hom ord "c" (fn v => Hom.mkFunction rf0 v)
  in
    assertTrue( Hom.eq(h0,Hom.id) )
  end

  fun testId00 () =
  let
    val vars = ["a","b","c","d"]
    val ord  = transform (MaxLeaves 3) (flatOrder vars)
    val ord' = transform Id ord
  in
    assertTrue( Order.eq( ord, ord' ) )
  end

  fun testShuffle00 () =
  let
    val vars = ["a","b","c","d"]
    val ord  = flatOrder vars
    val ord' = transform Shuffle ord
  in
    assertTrue( not (Order.eq( ord, ord' )) )
  end

  fun testShuffle01 () =
  let
    val vars = ["a","b","c","d"]
    val ord  = transform (MaxLeaves 3) (flatOrder vars)
    val ord' = transform Shuffle ord
  in
    assertTrue( not (Order.eq( ord, ord' )) )
  end

  fun testIdentifier00 () =
  let
    val vars = ["a","b","c","d"]
    val ord  = flatOrder vars
    val id   = identifier ord [3]
  in
    assertTrue( id = SOME "a" )
  end

  fun testIdentifier01 () =
  let
    val vars = ["a","b","c","d"]
    val ord  = flatOrder vars
    val id   = identifier ord [2]
  in
    assertTrue( id = SOME "b" )
  end

  fun testIdentifier02 () =
  let
    val vars = ["a","b","c","d"]
    val ord  = flatOrder vars
    val id   = identifier ord [0]
  in
    assertTrue( id = SOME "d" )
  end

  fun testIdentifier03 () =
  let
    val vars = []
    val ord  = flatOrder vars
    val id   = identifier ord [0]
  in
    assertTrue( id = NONE )
  end

  fun testIdentifier04 () =
  let
    val vars = ["a","b","c","d"]
    val ord  = transform Anonymise (transform (MaxLeaves 3) (flatOrder vars))
    val id   = identifier ord [1,0]
  in
    assertTrue( id = SOME "a" )
  end

  fun testIdentifier05 () =
  let
    val vars = ["a","b","c","d"]
    val ord  = transform Anonymise (transform (MaxLeaves 3) (flatOrder vars))
    val id   = identifier ord [0,0]
  in
    assertTrue( id = SOME "d" )
  end

  fun testIdentifier06 () =
  let
    val vars = ["a","b","c","d"]
    val ord  = transform Anonymise (transform (MaxLeaves 3) (flatOrder vars))
    val id   = identifier ord [0,3]
  in
    assertTrue( id = NONE )
  end

  fun testIdentifier07 () =
  let
    val vars = ["a","b","c","d"]
    val ord  = transform Anonymise (transform (MaxLeaves 3) (flatOrder vars))
    val id   = identifier ord [0,2]
  in
    assertTrue( id = SOME "b" )
  end

  fun testMaxLevels00 () =
  let
    val vars = ["a","b","c","d","e","f","g","h","i","j","k","l","m","n"]
    val ord  = flatOrder vars
    val o0    = transform (MaxLevels 0) ord
  in
    assertTrue( ord = o0 )
  end

  fun testMaxLevels01 () =
  let
    val vars = ["a","b","c","d","e","f","g","h","i","j","k","l","m","n"]
    val ord  = flatOrder vars
    val _    = transform (MaxLevels 5) ord
  in
    assertTrue( true )
  end

  fun testAuto00 () =
  let
    val vars = ["a","b","c","d","e","f","g","h","i","j","k","l","m","n"]
    val ord  = flatOrder vars
    val _    = transform (Auto (NONE, SOME 3)) ord
  in
    assertTrue( true )
  end

  fun testAuto01 () =
  let
    val vars = ["a","b","c","d","e","f","g","h","i","j","k","l","m","n"]
    val ord  = flatOrder vars
    val _    = transform (Auto (NONE, NONE)) ord
  in
    assertTrue( true )
  end

  fun testAuto02 () =
  let
    val vars = ["a","b","c","d","e","f","g","h","i","j","k","l","m","n"]
    val ord  = flatOrder vars
    val _    = transform (Auto (SOME 2, SOME 3)) ord
  in
    assertTrue( true )
  end

  fun suite () =
      Test.labelTests
      [ ("testFlatOrder00"     , testFlatOrder00   )
      , ("testHierOrder00"     , testHierOrder00   )
      , ("testMaxLeaves00"     , testMaxLeaves00   )
      , ("testMaxLeaves01"     , testMaxLeaves01   )
      , ("testMaxLeaves02"     , testMaxLeaves02   )
      , ("testMaxLeaves03"     , testMaxLeaves03   )
      , ("testFlatten00"       , testFlatten00     )
      , ("testSDD00"           , testSDD00         )
      , ("testSDD01"           , testSDD01         )
      , ("testAnonymise00"     , testAnonymise00   )
      , ("testHom00"           , testHom00         )
      , ("testHom01"           , testHom01         )
      , ("testHom02"           , testHom02         )
      , ("testId00"            , testId00          )
      , ("testShuffle00"       , testShuffle00     )
      , ("testShuffle01"       , testShuffle01     )
      , ("testIdentifier00"    , testIdentifier00  )
      , ("testIdentifier01"    , testIdentifier01  )
      , ("testIdentifier02"    , testIdentifier02  )
      , ("testIdentifier03"    , testIdentifier03  )
      , ("testIdentifier04"    , testIdentifier04  )
      , ("testIdentifier05"    , testIdentifier05  )
      , ("testIdentifier06"    , testIdentifier06  )
      , ("testIdentifier07"    , testIdentifier07  )
      , ("testMaxLevels00"     , testMaxLevels00   )
      , ("testMaxLevels01"     , testMaxLevels01   )
      , ("testAuto00"          , testAuto00        )
      , ("testAuto01"          , testAuto01        )
      , ("testAuto02"          , testAuto02        )
      ]

end
