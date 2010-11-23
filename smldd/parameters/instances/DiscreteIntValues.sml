(*--------------------------------------------------------------------------*)
structure DiscreteIntValues : VALUES = struct

(*--------------------------------------------------------------------------*)
structure SV = IntSortedVector
structure H  = Hash

(*--------------------------------------------------------------------------*)
(* Used by the unicity table *)
structure Definition (* : DATA *) = struct

  type t = ( SV.t * int )
  fun eq   ((x,_),(y,_)) = SV.eq(x,y)
  fun hash (x,_) = SV.hash x

  fun configure UnicityTableConfiguration.Name =
    UnicityTableConfiguration.NameRes "DiscreteIntValues"
  |   configure UnicityTableConfiguration.Buckets =
    UnicityTableConfiguration.BucketsRes 1000

end (* structure Definition *)

(*--------------------------------------------------------------------------*)
val discrete = true

(*--------------------------------------------------------------------------*)
type stored = Definition.t
type values = SV.t
type value  = int

(*--------------------------------------------------------------------------*)
structure UT = UnicityTableFunID ( structure Data = Definition )

(*--------------------------------------------------------------------------*)
fun uid (_,x) = x

(*--------------------------------------------------------------------------*)
(* Needed by the unicity table as a factory to create new values *)
fun mkValues v uid = ( v, uid )

(*--------------------------------------------------------------------------*)
fun mkStorable v = UT.unify (mkValues v)

(*--------------------------------------------------------------------------*)
fun mkUsable (v,_) = v

(*--------------------------------------------------------------------------*)
fun storedToList (v,_) = Util.IntVectorToList v

(*--------------------------------------------------------------------------*)
fun storedFromList xs =
let
  val v = (SV.fromList xs)
in
  UT.unify ( mkValues v)
end

(*--------------------------------------------------------------------------*)
val valueLt  = (op <)

(*--------------------------------------------------------------------------*)
fun storedEq (x,y) = uid x = uid y

(*--------------------------------------------------------------------------*)
fun storedLt (x,y) = uid x < uid y

(*--------------------------------------------------------------------------*)
fun storedHash (_,uid) = H.hashInt uid

(*--------------------------------------------------------------------------*)
fun storedEmpty (x,_) = SV.empty x

(*--------------------------------------------------------------------------*)
fun storedToString (x,_) = SV.toString x

(*--------------------------------------------------------------------------*)
val toString = SV.toString

(*--------------------------------------------------------------------------*)
val hash = SV.hash

(*--------------------------------------------------------------------------*)
val eq  = SV.eq

(*--------------------------------------------------------------------------*)
val length = SV.length

(*--------------------------------------------------------------------------*)
val empty = SV.empty

(*--------------------------------------------------------------------------*)
val e = mkStorable( SV.mkEmpty() )

(*--------------------------------------------------------------------------*)
(* Operations to manipulate values. Used by the cache. *)
structure Operations (* : OPERATION *) = struct

(*--------------------------------------------------------------------------*)
fun configure CacheConfiguration.Name =
  CacheConfiguration.NameRes "DiscreteIntValues"

(*--------------------------------------------------------------------------*)
type result        = stored
datatype operation = Union of stored list
                   | Inter of stored list
                   | Diff  of stored * stored

(*--------------------------------------------------------------------------*)
fun eq (l,r) =
let
  fun eqList ( [], [] ) = true
  |   eqList ( _ , [] ) = false
  |   eqList ( [], _  ) = false
  |   eqList ( x::xs, y::ys ) =
    if storedEq( x, y ) then
      eqList( xs, ys )
    else
      false
in
  case (l,r) of
    ( Union(xs), Union(ys) )     => eqList( xs,ys )
  | ( Inter(xs), Inter(ys) )     => eqList( xs,ys )
  | ( Diff(lx,ly), Diff(rx,ry) ) => storedEq(lx,rx) andalso storedEq(ly,ry)
  | ( _, _ )                     => false
end

(*--------------------------------------------------------------------------*)
fun hash x =
  let
    fun hashOperands( h0, xs ) =
      foldl (fn ( (_,uid), h ) => H.hashCombine( H.hashInt uid, h)) h0 xs
  in
    case x of
      Union(xs) => hashOperands( H.hashInt 15411567, xs)
    | Inter(xs) => hashOperands( H.hashInt 78995947, xs)
    | Diff( (_,luid), (_,ruid) ) =>
        H.hashCombine( H.hashInt 94165961
                     , H.hashCombine( H.hashInt luid, H.hashInt ruid )
                     )
  end

(*--------------------------------------------------------------------------*)
(* Evaluation an operation on valuations. Called by CacheFun. *)
fun apply operation =
  case operation of

    Union []     => raise DoNotPanic
  | Union( (x,_)::xs) =>
      let
        val v   = foldl (fn ( (v,_), res ) => SV.union(v,res)) x xs
      in
        UT.unify (mkValues v)
      end

  | Inter []     => raise DoNotPanic
  | Inter( (x,_)::xs) =>
      let
        val v = foldl (fn ( (v,_), res ) => SV.intersection(v,res))
                      x xs
      in
        UT.unify (mkValues v)
      end

  | Diff( (l,_), (r,_) ) => UT.unify (mkValues (SV.difference( l, r )))

(*--------------------------------------------------------------------------*)
end (* end structure Operations *)
(* Cache of operations *)

(*--------------------------------------------------------------------------*)
structure cache = CacheFun(structure Operation = Operations )

(*--------------------------------------------------------------------------*)
(* Operands should be sorted by caller *)
fun storedUnion xs =
  case xs of
    []  => raise DoNotPanic
  | [x] => x (* No need to cache *)
  | _   => cache.lookup( Operations.Union xs )

(*--------------------------------------------------------------------------*)
(* Operands should be sorted by caller *)
fun storedIntersection xs =
  case xs of
    []  => raise DoNotPanic
  | [x] => x (* No need to cache *)
  | _   => cache.lookup( Operations.Inter xs )

(*--------------------------------------------------------------------------*)
fun storedDifference(x,y) =
  if storedEq( x, y ) then
    e
  else
    cache.lookup( Operations.Diff(x,y) )

(*--------------------------------------------------------------------------*)
end (* DiscreteIntValues *)
