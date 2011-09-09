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
fun contains vec x =
let
  fun containsHelper first last =
    if last < first then
      NONE
    else if x < IntVector.sub(vec, first)
    orelse x > IntVector.sub(vec, last) then
      NONE
    else if x = IntVector.sub(vec, first) then
      SOME first
    else if x = IntVector.sub(vec, last) then
      SOME last
    else
    let
      val middleIndex = first + (Int.quot(last - first, 2))
      val middleValue = IntVector.sub(vec, middleIndex)
    in
      if x = middleValue then
        SOME middleIndex
      else if x < middleValue then
        containsHelper first (middleIndex - 1)
      else
        containsHelper (middleIndex + 1) last
    end
in
  containsHelper 0 (IntVector.length vec - 1)
end

(*--------------------------------------------------------------------------*)
fun insert vec x =
  case contains vec x of
    SOME _ => vec
  | NONE   =>
    let
      val vecLen = IntVector.length vec
      val inserted = ref false
      fun helper i =
        if not (!inserted) then
          if i >= vecLen orelse x < IntVector.sub(vec, i) then
          ( inserted := true
          ; x
          )
          else
            IntVector.sub(vec, i)
        else
          IntVector.sub(vec, i - 1)

    in
      IntVector.tabulate (vecLen + 1, helper)
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
    IntVector.fromList( foldl (fn (x,xs) => insertHelper xs (f x)) [] L)
  end

(*--------------------------------------------------------------------------*)
fun mapPartial f vec =
  if IntVector.length vec = 0 then
    vec
  else
  let
    val L = Util.IntVectorToList vec
  in
    IntVector.fromList( foldl (fn (x,xs) => case f x of
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
  fun combine (x1,x2) = Hash.hashCombine (Hash.hashInt x1, x2)
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
fun union (s1, s2) =
let

  val llen = IntVector.length s1
  val rlen = IntVector.length s2
  val tmp = IntArray.array(llen + rlen, 0)
  val len = ref 0

  fun loop i li ri =
    if li < llen andalso ri < rlen then
    let
      val l = IntVector.sub(s1, li)
      val r = IntVector.sub(s2, ri)
    in
      if l < r then
      ( IntArray.update(tmp, i, l)
      ; len := !len + 1
      ; loop (i+1) (li+1) ri
      )
      else if l > r then
      ( IntArray.update(tmp, i, r)
      ; len := !len + 1
      ; loop (i+1) li (ri+1)
      )
      else
      ( IntArray.update(tmp, i, l)
      ; len := !len + 1
      ; loop (i+1) (li+1) (ri+1)
      )
    end
    else
    let
      fun copy tmpi cont conti contlen =
        if conti < contlen then
        ( IntArray.update(tmp, tmpi, IntVector.sub(cont, conti))
        ; len := !len + 1
        ; copy (tmpi+1) cont (conti+1) contlen
        )
        else
        ()
    in
    (* Copy what remains in either s1 or s2 *)
    ( copy i s1 li llen
    ; copy i s2 ri rlen
    )
    end

  val _ = loop 0 0 0
in
  IntVector.tabulate(!len, fn i => IntArray.sub(tmp, i))
end

(*--------------------------------------------------------------------------*)
(* s1 and s2 MUST already be sorted *)
fun intersection (s1, s2) =
let

  val llen = IntVector.length s1
  val rlen = IntVector.length s2
  val tmp = IntArray.array(Int.min(llen, rlen), 0)
  val len = ref 0

  fun loop i li ri =
    if li < llen andalso ri < rlen then
    let
      val l = IntVector.sub(s1, li)
      val r = IntVector.sub(s2, ri)
    in
      if l = r then
      ( IntArray.update(tmp, i, l)
      ; len := !len + 1
      ; loop (i+1) (li+1) (ri+1)
      )
      else if l < r then
        loop i (li+1) ri
      else
        loop i li (ri+1)
    end
    else
      ()

  val _ = loop 0 0 0

in
  IntVector.tabulate(!len, fn i => IntArray.sub(tmp, i))
end

(*--------------------------------------------------------------------------*)
(* s1 and s2 MUST already be sorted *)
fun difference (s1, s2) =
let

  val llen = IntVector.length s1
  val rlen = IntVector.length s2
  val tmp = IntArray.array(llen, 0)
  val len = ref 0

  fun loop i li ri =
    if li < llen andalso ri < rlen then
    let
      val l = IntVector.sub(s1, li)
      val r = IntVector.sub(s2, ri)
    in
      if l = r then
        loop i (li+1) (ri+1)
      else if l < r then
      ( IntArray.update(tmp, i, l)
      ; len := !len + 1
      ; loop (i+1) (li+1) ri
      )
      else
        loop i li (ri+1)
    end
    else
    let
      fun copy tmpi cont conti contlen =
        if conti < contlen then
        ( IntArray.update(tmp, tmpi, IntVector.sub(cont, conti))
        ; len := !len + 1
        ; copy (tmpi+1) cont (conti+1) contlen
        )
        else
        ()
    in
      copy i s1 li llen
    end

  val _ = loop 0 0 0

in
  IntVector.tabulate(!len, fn i => IntArray.sub(tmp, i))
end

(*--------------------------------------------------------------------------*)
end (* structure IntSortedVector *)
