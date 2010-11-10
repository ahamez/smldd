(*--------------------------------------------------------------------------*)
structure BitWord = struct

(*--------------------------------------------------------------------------*)
type t  = Word32.word

(*--------------------------------------------------------------------------*)
exception Overflow

(*--------------------------------------------------------------------------*)
fun insert values x =
let
  val w = Word32.fromInt x
in
  if w > Word32.fromInt 31 then
    raise (Fail ((Int.toString x) ^ " > 31"))
  else
    Word32.orb( values, Word32.<<( Word32.fromInt 1, w) )
end

(*--------------------------------------------------------------------------*)
val eq = op =

(*--------------------------------------------------------------------------*)
fun lt (x:Word32.word,y:Word32.word) = x < y

(*--------------------------------------------------------------------------*)
val hash = Hash.hashWord

(*--------------------------------------------------------------------------*)
fun toString x =
let

  fun loop x i =
    if x = Word32.fromInt 0 then
      []
    else
      if Word32.andb( x, Word32.fromInt 1) <> Word32.fromInt 0 then
        Int.toString(i) :: (loop (Word32.>>( x, Word32.fromInt 1)) (i + 1))
      else
        (loop (Word32.>>( x, Word32.fromInt 1)) (i + 1))

in
  "{"
^ (String.concatWith "," (loop x 0))
^ "}"
end

(*--------------------------------------------------------------------------*)
fun length x =
let
  
  fun loop x =
    if x = Word32.fromInt 0 then
      Word32.fromInt 0
    else
      (Word32.andb( x, Word32.fromInt 1))
    + (loop (Word32.>>( x, Word32.fromInt 1)))

in
  Word32.toInt (loop x)
end    

(*--------------------------------------------------------------------------*)
fun empty x = x = (Word32.fromInt 0)

(*--------------------------------------------------------------------------*)
fun mkEmpty () = (Word32.fromInt 0)

(*--------------------------------------------------------------------------*)
fun union (s1,s2) = Word32.orb( s1, s2 )

(*--------------------------------------------------------------------------*)
fun intersection (s1,s2) = Word32.andb( s1, s2 )

(*--------------------------------------------------------------------------*)
fun difference (s1,s2) = Word32.andb( s1, Word32.notb s2 )

(*--------------------------------------------------------------------------*)
end (* structure BitWord *)
