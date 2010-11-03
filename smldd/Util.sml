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
fun sort extract lt xs =
let

  fun helper []      = []
  |   helper (x::xs) =
    let
      val x'    = extract x
      val (left,right)  = List.partition (fn y => lt( extract y , x' ) ) xs
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
let

  val threshold = 10000000000
  val precision = 2

  fun helper mant dotMant exp =
  let
    val (q,r) = IntInf.quotRem( mant, IntInf.fromInt 10 )
  in
    if q = 0 then
    let
      val ( dotMant', _ ) = foldl (fn ( x, ( acc, pow) ) =>
                                    ( acc + x * (IntInf.pow( 10, pow ))
                                    , pow - 1
                                    )
                                  )
                                  ( 0, precision - 1 )
                                  dotMant
    in
      ( mant, dotMant', exp )
    end
    else
    let
      val dotMant' = if length dotMant >= precision then
                       r::(List.take( dotMant, precision - 1 ))
                     else
                       r::dotMant
    in
      helper q dotMant' (exp + 1)
    end
  end

in
  if x < threshold then
    IntInf.toString x
  else
  let
    val (a,b,c) = helper x [] 0
  in
    IntInf.toString a ^ "." ^ (IntInf.toString b) ^ "E" ^ (IntInf.toString c)
  end
end

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
fun explodeRightBy xs i =
let

  fun helper ( x, [] ) = [[x]]
  |   helper ( x, Y as (y::ys) ) =
    if length y = i then
      [x] :: Y
    else
      (x::y)::ys

in

  if i < 0 then
    raise Domain
  else if i > length xs then
    raise Subscript
  else
    foldr helper [] xs

end

(*--------------------------------------------------------------------------*)
end (* structure Util *)
