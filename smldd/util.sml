(*--------------------------------------------------------------------------*)

fun VectorToList ( vec : 'a Vector.vector ) =
  Vector.foldr (fn (elm,acc) => elm::acc ) [] vec

(*--------------------------------------------------------------------------*)

fun IntVectorToList ( vec : IntVector.vector ) =
  IntVector.foldr (fn (elm,acc) => elm::acc ) [] vec

(*--------------------------------------------------------------------------*)
