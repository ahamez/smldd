structure TestDot =
struct

open SDD

val values = Values o IntVector.fromList

val toDot      = SDD.toDot ShowHierarchy
val toDotShare = SDD.toDot ShowSharing

fun test00 () =
let
  val s0 = node( 0 , values [1,2,3], one )
  val x0 = node( 10, Nested s0, one )

  val dot = toDot x0
  val dotFile = TextIO.openOut "testDot00.dot"
in
  TextIO.outputSubstr ( dotFile, Substring.extract(dot,0, NONE) )
end

fun test01 () =
let
  val s0 = node( 0 , values [1,2,3], one )
  val x0 = node( 10, Nested s0, one )
  val x1 = node (11, Nested x0, x0 )

  val dot = toDot x1
  val dotFile = TextIO.openOut "testDot01.dot"
in
  TextIO.outputSubstr ( dotFile, Substring.extract(dot,0, NONE) )
end

fun test02 () =
let
  val s0 = node( 0 , values [1,2,3], one )
  val x0 = node( 10, Nested s0, one )
  val x1 = node (11, Nested x0, x0 )

  val dot = toDotShare x1
  val dotFile = TextIO.openOut "testDot02.dot"
in
  TextIO.outputSubstr ( dotFile, Substring.extract(dot,0, NONE) )
end

fun test03 () =
let
  val s0 = node( 0 , values [1,2,3], one )
  val x0 = node( 10, Nested s0, one )
  val x1 = node (11, Nested s0, x0 )

  val dot = toDot x1
  val dotFile = TextIO.openOut "testDot03.dot"
in
  TextIO.outputSubstr ( dotFile, Substring.extract(dot,0, NONE) )
end

end (* structure TestDot *)

fun testDot () =
(
  TestDot.test00 ();
  TestDot.test01 ();
  TestDot.test02 ();
  TestDot.test03 ();
  ()
)
