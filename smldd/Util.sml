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

  fun helper [] = []
  |   helper (x::[]) = [x]
  |   helper (x1::x2::xs) =
  let
    val m = Word.mod ((MLton.Random.rand()) , (Word.fromInt 2))
    val r = if  m = Word.fromInt 0 then
              true
            else
              false
  in
    if r then
      x1::x2::(helper xs)
    else
      x2::x1::(helper xs)
  end

in
  helper xs
end

(*--------------------------------------------------------------------------*)
end (* structure Util *)
