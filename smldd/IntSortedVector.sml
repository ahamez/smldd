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
fun unionHelper acc ( [], R ) = acc @ R
|   unionHelper acc ( L, [] ) = acc @ L
|   unionHelper acc ( L as (l::ls), R as (r::rs) ) =
  if l > r then
    unionHelper (acc @ [r]) ( L, rs )
  else if l < r then
    unionHelper (acc @ [l]) ( ls, R )
  else
    unionHelper (acc @ [l]) ( ls, rs )

fun union (s1,s2) =
  IntVector.fromList (unionHelper []
                                  ( Util.IntVectorToList s1
                                  , Util.IntVectorToList s2
                                  )
                     )

(*--------------------------------------------------------------------------*)
(* s1 and s2 MUST already be sorted *)
fun interHelper acc ( [], _ ) = acc
|   interHelper acc ( _, [] ) = acc
|   interHelper acc ( L as (l::ls), R as (r::rs) ) =
  if l = r then
    interHelper (acc @ [r]) ( ls, rs )
  else if l < r then
    interHelper acc ( ls, R )
  else
    interHelper acc ( L, rs )

fun intersection (s1,s2) =
  IntVector.fromList (interHelper []
                                  ( Util.IntVectorToList s1
                                  , Util.IntVectorToList s2
                                  )
                     )

(*--------------------------------------------------------------------------*)
(* s1 and s2 MUST already be sorted *)
fun diffHelper acc ( [], _ ) = acc
|   diffHelper acc ( L, [] ) = acc @ L
|   diffHelper acc ( L as (l::ls), R as (r::rs) ) =
  if l = r then
    diffHelper acc ( ls, rs )
  else if l < r then
    diffHelper (acc @ [l]) ( ls, R )
  else
    diffHelper acc ( L, rs )

fun difference (s1,s2) =
  IntVector.fromList (diffHelper []
                                 ( Util.IntVectorToList s1
                                 , Util.IntVectorToList s2
                                 )
                     )

(*--------------------------------------------------------------------------*)
end (* structure IntSortedVector *)
