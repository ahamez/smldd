structure TestOrder =
struct

  open SMLUnit.Assert
  structure Test = SMLUnit.Test
  open StringOrder

  fun testFlatOrder00 () =
  let
    val vars = ["a","b","c","d"]
    val ord  = flatOrder vars
    (*val _ = print "\n"
    val _ = print (toString ord)*)
  in
    assertTrue( true )
  end

  fun testHierOrder00 () =
  let
    val ord0  = flatOrder ["a","b","c","d"]
    val ord1  = flatOrder ["d","e","f","g"]
    val ord2  = addHierarchicalNode (mkOrder()) "x" ord0
    val ord3  = addHierarchicalNode ord2 "y" ord1
    (*val _ = print "\n"
    val _ = print (toString ord3)*)
  in
    assertTrue( true )
  end

  fun testMaxLeaves00 () =
  let
    val vars = ["a","b","c","d","e","f","g","h","i","j","k","l","m","n","o"]
    val ord  = flatOrder vars
    val ord' = transform (MaxLeaves 5) ord
    (*val _ = print "\n"
    val _ = print (toString ord')*)
  in
    assertTrue( true )
  end

  fun testMaxLeaves01 () =
  let
    val vars = ["a","b","c","d","e","f","g","h","i","j","k","l","m","n"]
    val ord  = flatOrder vars
    val ord' = transform (MaxLeaves 3) ord
    (*val _ = print "\n"
    val _ = print (toString ord')*)
  in
    assertTrue( true )
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
    assertTrue( s0 = o0 )
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
    assertTrue( s0 = o1 )
  end

  fun testAnonymise00 () =
  let
    val ord = flatOrder ["a","b","c","d"]
    val ord'  = transform Anonymise (transform (MaxLeaves 3) ord)
    val cst = IntSortedVector.fromList [0]
    val vst = SDD.Values cst
    fun f _ = cst
    val s0  = SDD ord' f
    val o0  = SDD.node( 0
                      , SDD.Nested (SDD.fromList [(2,vst),(1,vst),(0,vst)])
                      , SDD.one
                      )
    val o1  = SDD.node( 1, SDD.Nested (SDD.node(0,vst,SDD.one)), o0 )
  in
    assertTrue( o1 = s0 )
  end

  fun testHom00 () =
  let
    fun f0 _ = IntSortedVector.fromList [1,2,3]
    val rf0  = ref f0
    val vars  = ["a","b","c","d","e","f","g","h","i","j","k","l","m","n"]
    val ord   = flatOrder vars
    val h0    = hom ord "i" (fn v => Hom.mkFunction rf0 v)
    val o0    = Hom.mkFunction rf0 5
  in
    assertTrue( h0 = o0 )
  end

  fun testHom01 () =
  let
    fun f0 _ = IntSortedVector.fromList [1,2,3]
    val rf0  = ref f0
    val vars  = ["a","b","c","d"]
    val ord  = transform (MaxLeaves 3) (flatOrder vars)
    val h0    = hom ord "c" (fn v => Hom.mkFunction rf0 v)
    val o0    = Hom.mkNested (Hom.mkFunction rf0 1) 0
  in
    assertTrue( h0 = o0 )
  end

  fun suite () =
      Test.labelTests
      [ ("testFlatOrder00"     , testFlatOrder00   )
      , ("testHierOrder00"     , testHierOrder00   )
      , ("testMaxLeaves00"     , testMaxLeaves00   )
      , ("testMaxLeaves01"     , testMaxLeaves01   )
      , ("testFlatten00"       , testFlatten00     )
      , ("testSDD00"           , testSDD00         )
      , ("testSDD01"           , testSDD01         )
      , ("testAnonymise00"     , testAnonymise00   )
      , ("testHom00"           , testHom00         )
      , ("testHom01"           , testHom01         )
      ]

end
