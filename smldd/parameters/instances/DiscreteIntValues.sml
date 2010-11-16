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
type stored = Definition.t ref
type values = SV.t
type value  = int

(*--------------------------------------------------------------------------*)
structure UT = UnicityTableFunID ( structure Data = Definition )

(*--------------------------------------------------------------------------*)
fun uid (ref(_,x)) = x

(*--------------------------------------------------------------------------*)
(* Needed by the unicity table as a factory to create new values *)
fun mkValues v uid = ( v, uid )

(*--------------------------------------------------------------------------*)
fun mkStorable v = UT.unify (mkValues v)

(*--------------------------------------------------------------------------*)
fun mkUsable (ref(v,_)) = v

(*--------------------------------------------------------------------------*)
fun storedToList (ref(v,_)) = Util.IntVectorToList v

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
fun storedLt (x,y) = uid x < uid y

(*--------------------------------------------------------------------------*)
fun storedHash (ref(_,uid)) = H.hashInt uid

(*--------------------------------------------------------------------------*)
fun storedEmpty (ref(x,_)) = SV.empty x

(*--------------------------------------------------------------------------*)
fun storedToString (ref(x,_)) = SV.toString x

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
fun storedMkEmpty() = e

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
  case (l,r) of
    ( Union(xs), Union(ys) )     => xs = ys
  | ( Inter(xs), Inter(ys) )     => xs = ys
  | ( Diff(lx,ly), Diff(rx,ry) ) => lx = rx andalso ly = ry
  | ( _, _ )                     => false

(*--------------------------------------------------------------------------*)
fun hash x =
  let
    fun hashOperands( h0, xs ) =
      foldl (fn ( ref(_,uid), h ) => H.hashCombine( H.hashInt uid, h)) h0 xs
  in
    case x of
      Union(xs) => hashOperands( H.const 15411567, xs)
    | Inter(xs) => hashOperands( H.const 78995947, xs)
    | Diff(ref(_,luid),ref(_,ruid)) =>
        H.hashCombine( H.const 94165961
                     , H.hashCombine( H.hashInt luid, H.hashInt ruid )
                     )
  end

(*--------------------------------------------------------------------------*)
(* Evaluation an operation on valuations. Called by CacheFun. *)
fun apply operation =
  case operation of

    Union []     => raise DoNotPanic
  | Union(ref(x,_)::xs) =>
      let
        val v   = foldl (fn (ref(v,_),res) => SV.union(v,res)) x xs
      in
        UT.unify (mkValues v)
      end

  | Inter []     => raise DoNotPanic
  | Inter(ref(x,_)::xs) =>
      let
        val v = foldl (fn (ref(v,_),res) => SV.intersection(v,res))
                      x xs
      in
        UT.unify (mkValues v)
      end

  | Diff( ref(l,_), ref(r,_) ) =>
      let
        val v   = SV.difference( l, r )
        val hsh = SV.hash v
      in
        UT.unify (mkValues v)
      end

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
  if x = y then
    storedMkEmpty()
  else
    cache.lookup( Operations.Diff(x,y) )

(*--------------------------------------------------------------------------*)
end (* DiscreteIntValues *)
