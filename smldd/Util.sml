(*--------------------------------------------------------------------------*)
structure Util = struct

(*--------------------------------------------------------------------------*)
fun VectorToList (vec : 'a Vector.vector) =
  Vector.foldr (fn (elm,acc) => elm::acc) [] vec

(*--------------------------------------------------------------------------*)
fun IntVectorToList (vec : IntVector.vector) =
  IntVector.foldr (fn (elm,acc) => elm::acc) [] vec

(*--------------------------------------------------------------------------*)
fun id x = x

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
end (* structure Util *)
