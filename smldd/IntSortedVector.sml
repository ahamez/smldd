(* TODO: do not use intermediary list for simple tasks like insert... *)
(*--------------------------------------------------------------------------*)
structure IntSortedVector = struct

(*--------------------------------------------------------------------------*)
type t  = IntVector.vector

(*--------------------------------------------------------------------------*)
local (* fromList, map, mapPartial *)

(*--------------------------------------------------------------------------*)
fun insertHelper [] x             = [x]
|   insertHelper (L as (l::ls)) x =
if x = l then
  L
else if x < l then
  x::L
else
  l::(insertHelper ls x)

(*--------------------------------------------------------------------------*)
in (* local fromList, map, mapPartial *)

(*--------------------------------------------------------------------------*)
fun insert vec x =
let
  val L = Util.IntVectorToList vec
in
  IntVector.fromList (insertHelper L x)
end

(*--------------------------------------------------------------------------*)
fun fromList [] = IntVector.fromList []
|   fromList xs =
  IntVector.fromList (foldl (fn (x,l) => insertHelper l x) [] xs)

(*--------------------------------------------------------------------------*)
fun map f vec =
  if IntVector.length vec = 0 then
    vec
  else
  let
    val L = Util.IntVectorToList vec
  in
    IntVector.fromList( foldl (fn (x,xs) => insertHelper xs (f x)) [] L )
  end

(*--------------------------------------------------------------------------*)
fun mapPartial f vec =
  if IntVector.length vec = 0 then
    vec
  else
  let
    val L = Util.IntVectorToList vec
  in
    IntVector.fromList( foldl (fn (x,xs) =>
                                case f x of
                                  NONE    => xs
                                | SOME x' => insertHelper xs x'
                              )
                              []
                              L
                      )
  end

(*--------------------------------------------------------------------------*)
end (* local fromList, map, mapPartial *)

(*--------------------------------------------------------------------------*)
fun eq (l,r) =
let
  fun helper 0 = true
  |   helper i =
    if IntVector.sub(l,i-1) = IntVector.sub(r,i-1) then
      helper (i - 1)
    else
      false
in
  if IntVector.length l <> IntVector.length r then
    false
  else
    helper (IntVector.length l)
end

(*--------------------------------------------------------------------------*)
fun hash vec =
let
  fun combine (x1,x2) = Hash.hashCombine ( Hash.hashInt x1, x2 )
in
  IntVector.foldl combine (Hash.hashInt 42) vec
end

(*--------------------------------------------------------------------------*)
fun toString vec =
let
  val l = List.map (fn x => Int32.toString x) (Util.IntVectorToList vec)
  val s = String.concatWith "," l
in
  "{" ^ s ^ "}"
end

(*--------------------------------------------------------------------------*)
val length = IntVector.length

(*--------------------------------------------------------------------------*)
fun empty vec = IntVector.length vec = 0

(*--------------------------------------------------------------------------*)
fun mkEmpty () = IntVector.fromList []

(*--------------------------------------------------------------------------*)
(* s1 and s2 MUST already be sorted *)
fun union ( s1, s2 ) =
let
  fun helper acc ~1 ~1 = acc
  |   helper acc ~1 y  = (Util.IntVectorRangeToList s2 0 y ) @ acc
  |   helper acc x ~1  = (Util.IntVectorRangeToList s1 0 x ) @ acc
  |   helper acc x y   =
  let
    val l = IntVector.sub( s1, x )
    val r = IntVector.sub( s2, y )
  in
    if l > r then
      helper (l::acc) (x-1) y
    else if l < r then
      helper (r::acc) x (y-1)
    else
      helper (l::acc) (x-1) (y-1)
  end
in
  IntVector.fromList( helper []
                             (IntVector.length s1 - 1)
                             (IntVector.length s2 - 1)
                    )
end

(*--------------------------------------------------------------------------*)
(* s1 and s2 MUST already be sorted *)
fun intersection ( s1, s2 ) =
let
  fun helper acc ~1 _ = acc
  |   helper acc _ ~1 = acc
  |   helper acc x y  =
  let
    val l = IntVector.sub( s1, x )
    val r = IntVector.sub( s2, y )
  in
    if l = r then
      helper (l::acc) (x-1) (y-1)
    else if l > r then
      helper acc (x-1) y
    else
      helper acc x (y-1)
  end
in
  IntVector.fromList( helper []
                             (IntVector.length s1 - 1)
                             (IntVector.length s2 - 1)
                    )
end

(*--------------------------------------------------------------------------*)
(* s1 and s2 MUST already be sorted *)
fun difference (s1,s2) =
let
  fun helper acc ~1 ~1 = acc
  |   helper acc ~1 _  = acc
  |   helper acc x ~1  = (Util.IntVectorRangeToList s1 0 x) @ acc
  |   helper acc x y   =
  let
    val l = IntVector.sub( s1, x )
    val r = IntVector.sub( s2, y )
  in
    if l = r then
      helper acc (x-1) (y-1)
    else if l > r then
      helper (l::acc) (x-1) y
    else
      helper acc x (y-1)
  end
in
  IntVector.fromList( helper []
                             (IntVector.length s1 - 1)
                             (IntVector.length s2 - 1)
                    )
end

(*--------------------------------------------------------------------------*)
end (* structure IntSortedVector *)
