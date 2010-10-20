structure TestDot =
struct

open SDD

val values = Values o IntVector.fromList

val toDot      = Tools.toDot Tools.ShowHierarchy
val toDotShare = Tools.toDot Tools.ShowSharing

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

fun test04 () =
let
  val x0 = node (11, Nested one, one )

  val dot = toDot x0
  val dotFile = TextIO.openOut "testDot04.dot"
in
  TextIO.outputSubstr ( dotFile, Substring.extract(dot,0, NONE) )
end

fun test05 () =
let
  val x0 = node (11, Nested one, one )

  val dot = toDotShare x0
  val dotFile = TextIO.openOut "testDot05.dot"
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
  TestDot.test04 ();
  TestDot.test05 ();
  ()
)
