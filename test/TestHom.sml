structure TestHom =
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
  fun testId00 () =
    assertTrue( SDD.eq(eval id one,one) )

(*--------------------------------------------------------------------------*)
  fun testId01 () =
  let
    val s0 = node( 0, values [0,1], one )
  in
    assertTrue( SDD.eq(eval id s0, s0) )
  end

(*--------------------------------------------------------------------------*)
  fun testCons00 () =
  let
    val s0 = node( 0, values [0], one )
    val x1 = node( 0, Nested s0, one )
    val h0 = mkCons 1 (Nested s0) id
    val c0 = eval h0 x1
    val y0 = node( 1, Nested s0, x1 )
  in
    assertTrue( SDD.eq(c0 ,y0) )
  end

(*--------------------------------------------------------------------------*)
  fun testCons01 () =
  let
    val s0 = node( 0, values [0], one )
    val x1 = node( 0, Nested s0, one )
    val h0 = mkCons 1 (Nested s0) id
    val c0 = eval h0 x1
    val c1 = eval h0 x1
  in
    assertTrue( SDD.eq(c0,c1) )
  end

(*--------------------------------------------------------------------------*)
  fun testCons02 () =
  let
    val s0 = node( 0, values[0], one )
    val h0 = mkCons 0 (values [0]) id
    val c0 = eval h0 one
  in
    assertTrue( SDD.eq(c0,s0) )
  end

(*--------------------------------------------------------------------------*)
  fun testConst00 () =
  let
    val s0 = node( 0, values [0], one )
    val x1 = node( 0, Nested s0, one )
    val h0 = mkConst one
    val c0 = eval h0 x1
  in
    assertTrue( SDD.eq(c0,one) )
  end

(*--------------------------------------------------------------------------*)
  fun testConst01 () =
  let
    val h0 = mkConst one
    val c0 = eval h0 zero
  in
    assertTrue( SDD.eq(c0,one) )
  end

(*--------------------------------------------------------------------------*)
fun testNested00 () =
let
  val s0 = node( 0, (values[0]), one)
  val x0 = node( 0, Nested s0, one )
  val h0 = mkNested id 0
  val r0 = eval h0 x0
in
  assertTrue( SDD.eq(r0,x0) )
end

(*--------------------------------------------------------------------------*)
fun testNested01 () =
let
  val h0 = mkNested id 0
in
  assertTrue( Hom.eq(h0,id) )
end

(*--------------------------------------------------------------------------*)
fun testUnion00 () =
let
  val h0 = mkUnion [id]
  val s0 = node( 0, values [0,1,2], one)
  val s1 = eval h0 s0
in
  assertTrue( SDD.eq(s1,s0) )
end

(*--------------------------------------------------------------------------*)
fun testUnion01 () =
let
  val h0 = mkUnion [id,id,id]
  val s0 = node( 0, values [0,1,2], one)
  val s1 = eval h0 s0
in
  assertTrue( SDD.eq(s1,s0) )
end


(*--------------------------------------------------------------------------*)
fun testFixpoint00 () =
let
  val h0 = mkFixpoint id
  val s0 = node( 0, (values [0,1]), one)
  val s1 = eval h0 s0
in
  assertTrue( SDD.eq(s0,s1) )
end

(*--------------------------------------------------------------------------*)

  fun suite () =
      Test.labelTests
      [ ("testId00"            , testId00            )
      , ("testId01"            , testId01            )
      , ("testCons00"          , testCons00          )
      , ("testCons01"          , testCons01          )
      , ("testCons02"          , testCons02          )
      , ("testConst00"         , testConst00         )
      , ("testNested00"        , testNested00        )
      , ("testNested01"        , testNested01        )
      , ("testUnion00"         , testUnion00         )
      , ("testUnion01"         , testUnion01         )
      , ("testFixpoint00"      , testFixpoint00      )
      ]

(*--------------------------------------------------------------------------*)

end
