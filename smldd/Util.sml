(*--------------------------------------------------------------------------*)
structure Util = struct

(*--------------------------------------------------------------------------*)
fun VectorToList ( vec : 'a Vector.vector ) =
  Vector.foldr (fn (elm,acc) => elm::acc ) [] vec

(*--------------------------------------------------------------------------*)
fun IntVectorToList ( vec : IntVector.vector ) =
  IntVector.foldr (fn (elm,acc) => elm::acc ) [] vec

(*--------------------------------------------------------------------------*)
fun sortUnique extract lt gt xs =
let

  fun helper []      = []
  |   helper (x::xs) =
    let
      val x'    = extract x
      val left  = List.filter (fn y => lt( extract y , x' ) ) xs
      val right = List.filter (fn y => gt( extract y , x' ) ) xs
    in
      helper left @ [x] @ helper right
    end

in
  helper xs
end

(*--------------------------------------------------------------------------*)
fun id x = x

(*--------------------------------------------------------------------------*)
fun shuffle xs =
let

  val _ = case MLton.Random.seed() of
             NONE  => MLton.Random.srand (Word.fromInt 42)
          | SOME v => MLton.Random.srand v

  val a = Array.fromList xs

  fun loop 0 = a
  |   loop i =
  let
    val j   = Word.toInt( Word.mod( MLton.Random.rand(), Word.fromInt i ) )
    val tmp = Array.sub( a, j )
    val _   = Array.update( a, j, Array.sub( a, i ) )
    val _   = Array.update( a, i, tmp )
  in
    loop (i-1)
  end

in
  Array.foldr (fn (x,acc) => x::acc) [] (loop ((Array.length a) -1))
end

(*--------------------------------------------------------------------------*)
fun IntInfToHumanString x =
  if x < 1000000 then
    IntInf.toString x
  else
    Real.fmt (StringCvt.SCI (SOME 2)) (Real.fromLargeInt x)

(*--------------------------------------------------------------------------*)
fun splitAt xs i =
let

  fun helper [] _      = ( [], [])
  |   helper xs 0      = ( [], xs )
  |   helper (x::xs) i =
  let
    val ( a, b ) = helper xs (i - 1)
  in
    ( x::a, b )
  end

in
  if i < 0 orelse i > length xs then
    raise Subscript
  else
    helper xs i
end

(*--------------------------------------------------------------------------*)
end (* structure Util *)
