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
  if (IntVector.length l) <> (IntVector.length r) then
    false
  else
    let
      fun helper 0 = true
      |   helper i =
        if IntVector.sub(l,i-1) = IntVector.sub(r,i-1) then
          helper (i - 1)
        else
          false
    in
      helper (IntVector.length l)
    end

(*--------------------------------------------------------------------------*)
fun hash vec =
  let
    fun helper (x1,x2) = Hash.hashCombine ( Hash.hashInt x1, x2 )
  in
    IntVector.foldl helper (Hash.hashInt 42) vec
  end

(*--------------------------------------------------------------------------*)
fun toString vec =
let
  val l = List.map (fn x => Int32.toString x ) (Util.IntVectorToList vec)
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
fun unionHelper ( [], R ) = R
|   unionHelper ( L, [] ) = L
|   unionHelper ( L as (l::ls), R as (r::rs) ) =
  if l > r then
    r::unionHelper( L, rs )
  else if l < r then
    l::unionHelper( ls, R )
  else
    l::unionHelper( ls, rs )

fun union (s1,s2) =
  IntVector.fromList (unionHelper ( Util.IntVectorToList s1
                                  , Util.IntVectorToList s2)
                     )

(*--------------------------------------------------------------------------*)
(* s1 and s2 MUST already be sorted *)
fun interHelper ( [], _ ) = []
|   interHelper ( _, [] ) = []
|   interHelper ( L as (l::ls), R as (r::rs) ) =
  if l = r then
    r::interHelper( ls, rs )
  else if l < r then
    interHelper( ls, R )
  else
  interHelper( L, rs )

fun intersection (s1,s2) =
  IntVector.fromList (interHelper ( Util.IntVectorToList s1
                                  , Util.IntVectorToList s2)
                     )

(*--------------------------------------------------------------------------*)
(* s1 and s2 MUST already be sorted *)
fun diffHelper ( [], _ ) = []
|   diffHelper ( L, [] ) = L
|   diffHelper ( L as (l::ls), R as (r::rs) ) =
  if l = r then
    diffHelper( ls, rs )
  else if l < r then
    l::diffHelper( ls, R )
  else
    diffHelper( L, rs )

fun difference (s1,s2) =
  IntVector.fromList (diffHelper ( Util.IntVectorToList s1
                                 , Util.IntVectorToList s2)
                     )

(*--------------------------------------------------------------------------*)
end (* structure IntSortedVector *)
