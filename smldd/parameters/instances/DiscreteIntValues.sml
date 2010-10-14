structure DiscreteIntValues : VALUES =
struct

  (*----------------------------------------------------------------------*)
  type t  = IntVector.vector

  (*----------------------------------------------------------------------*)
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

  (*----------------------------------------------------------------------*)
  fun lt (l,r) =
    if (IntVector.length l) = 0 then
      true
    else if (IntVector.length r) = 0 then
      false
    else if IntVector.sub(l,0) < IntVector.sub(r,0) then
      true
    else if IntVector.sub(l,0) > IntVector.sub(r,0) then
      false
    else
      lt( IntVectorSlice.vector( IntVectorSlice.slice (l, 1, NONE))
        , IntVectorSlice.vector( IntVectorSlice.slice (r, 1, NONE))
        )

  (*----------------------------------------------------------------------*)
  fun hash vec =
    let
      fun helper (x1,x2) = Word32.xorb ( MLton.hash x1, x2 )
    in
      IntVector.foldl helper (Word32.fromInt 42) vec
    end

  (*----------------------------------------------------------------------*)
  fun toString vec =
  let
    val l = map (fn x => Int32.toString x ) (IntVectorToList vec)
    val s = String.concatWith "," l
  in
    "{" ^ s ^ "}"
  end

  (*----------------------------------------------------------------------*)
  val length = IntVector.length

  (*----------------------------------------------------------------------*)
  fun empty vec = IntVector.length vec = 0

  (*----------------------------------------------------------------------*)
  fun mkEmpty vec = IntVector.fromList []

  (*----------------------------------------------------------------------*)
  (* s1 and s2 MUST already be sorted *)
  fun unionHelper (L,R) =
    case L of
      []      => R
    | (l::ls) =>
        case R of
          []      => L
        | (r::rs) => if l > r then
                       r::(unionHelper(L,rs))
                     else if l < r then
                       l::(unionHelper(ls,R))
                     else
                       l::(unionHelper(ls,rs))

  fun union (s1,s2) =
    IntVector.fromList (unionHelper (IntVectorToList s1, IntVectorToList s2))

  (*----------------------------------------------------------------------*)
  (* s1 and s2 MUST already be sorted *)
  fun interHelper (L,R) =
    case L of
      []      => []
    | (l::ls) =>
        case R of
          []      => []
        | (r::rs) => if l = r then
                       r::(interHelper(ls,rs))
                     else if l < r then
                       interHelper(ls,R)
                     else
                       interHelper(L,rs)

  fun intersection (s1,s2) =
    IntVector.fromList (interHelper (IntVectorToList s1, IntVectorToList s2))

  (*----------------------------------------------------------------------*)
  (* s1 and s2 MUST already be sorted *)
  fun diffHelper (L,R) =
    case L of
      []      => []
    | (l::ls) =>
        case R of
          []      => L
        | (r::rs) => if l = r then
                       diffHelper(ls,rs)
                     else if l < r then
                       l::(diffHelper(ls,R))
                     else
                       diffHelper(L,rs)

  fun difference (s1,s2) =
    IntVector.fromList (diffHelper (IntVectorToList s1, IntVectorToList s2))

  (*----------------------------------------------------------------------*)

end (* DiscreteIntValues *)
