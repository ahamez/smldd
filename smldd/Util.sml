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
(* Our own take function which does not check bounds *)
fun take (l, n) =
let
   fun loop (l, n, ac) =
      if n > 0 then
        case l of
          [] => rev ac
        | x :: l => loop (l, n - 1, x::ac)
      else
        rev ac
in
  if n < 0 then
    raise Subscript
  else
    loop (l, n, [])
end

(*--------------------------------------------------------------------------*)
(* Export an IntInf to a string in scientific notation *)
fun IntInfToString x thresh prec =
let

  val threshold = case thresh of
                    NONE   => 10000000000
                  | SOME t => t

  val precision = case prec of
                    NONE   => 2
                  | SOME p => p

  fun helper mant dotMant exp =
  let
    val (q,r) = IntInf.quotRem( mant, IntInf.fromInt 10 )
  in
    if q = 0 then
    let

      val l = let
                val len = length dotMant
              in
                if len <= precision then
                  dotMant @ (List.tabulate (precision - len + 1, fn _ => 0))
                else
                  dotMant
              end

      val (l',carry) = if List.last l > 5 then
                         foldr (fn ( x, ( acc, carry ) ) =>
                                  if carry then
                                    if x = 9 then
                                      ( 0::acc, true )
                                    else
                                      ( (x+1)::acc, false )
                                  else
                                    ( x::acc, false )
                                )
                                ( [], true )
                                (List.take (l, precision))
                       else
                         ( l, false )

      val dotMant' = (String.concat (map (fn x => (IntInf.toString x))
                                         (List.take ( l', precision ))
                                    )
                     )

      val mant' = if carry then mant + 1 else mant

    in
      ( IntInf.toString mant', dotMant', Int.toString exp )
    end
    else
    let
      val dotMant' =  r::(take( dotMant, precision ))
      (*if length dotMant > precision then
                             r::(List.take( dotMant, precision ))
                           else
                             r::dotMant*)
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
    a ^ "." ^ b ^ "E" ^ c
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
