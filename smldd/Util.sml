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
end (* structure Util *)
