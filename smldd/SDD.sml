(*--------------------------------------------------------------------------*)
signature SDD = sig

  eqtype SDD
  type variable
  type values

  datatype valuation      = Nested of SDD
                          | Values of values

  val zero                : SDD
  val one                 : SDD
  val node                : variable * valuation * SDD -> SDD
  val nodeAlpha           : variable * (valuation * SDD) list -> SDD
  val fromList            : (variable * valuation ) list -> SDD

  val union               : SDD list -> SDD
  val intersection        : SDD list -> SDD
  val difference          : SDD * SDD -> SDD

  val lt                  : SDD * SDD -> bool
  val uid                 : SDD -> int
  val variable            : SDD -> variable
  val alpha               : SDD -> (valuation * SDD) list
  val hash                : SDD -> Hash.t

  val insert              : SDD list -> SDD -> SDD list

  val values              : valuation -> values
  val nested              : valuation -> SDD
  val hashValuation       : valuation -> Hash.t
  val eqValuation         : (valuation * valuation) -> bool
  val valuationToString   : valuation -> string

  val toString            : SDD -> string

  datatype 'a visitorMode = Cached | NonCached | Once of 'a
  type 'a visitor         =  (unit -> 'a)
                          -> (unit -> 'a)
                          -> (int -> variable -> (valuation * SDD) list -> 'a)
                          -> SDD
                          -> 'a
  val mkVisitor           : 'a visitorMode -> 'a visitor

  val stats               : unit -> string

  exception IncompatibleSDD
  exception IsNotANode
  exception IsNotValues
  exception IsNotNested

end

(*--------------------------------------------------------------------------*)
functor SDDFun ( structure Variable  : VARIABLE
               ; structure Values    : VALUES )
  : SDD
= struct

(*--------------------------------------------------------------------------*)
type variable     = Variable.t
type values       = Values.values
type storedValues = Values.stored

(*--------------------------------------------------------------------------*)
(* Define an SDD *)
structure Definition (* : DATA *) = struct

  datatype t    = iSDD of ( sdd * Hash.t * int )
  and sdd       = Zero
                | One
                | Node of  { variable : variable
                           , alpha : (storedValues * t ref) Vector.vector
                           }
                | HNode of { variable : variable
                           , alpha : ( t ref * t ref ) Vector.vector
                           }

  (* Compare two SDDs.
     At this point, we can't use the identifier to know if two SDDs are
     equals because this equality is called by the unicity table which is
     responsible for the generation of this id.= *)
  fun eq ( iSDD(lsdd,lh,_), iSDD(rsdd,rh,_) ) =
    if lh <> rh then
      false
    else
      case ( lsdd, rsdd ) of

        ( Zero, Zero ) => true
      | ( One, One   ) => true

      | ( Node{ variable=lvr, alpha=lalpha }
        , Node{ variable=rvr, alpha=ralpha } ) =>
            Variable.eq(lvr,rvr) andalso lalpha = ralpha

      | ( HNode{ variable=lvr, alpha=lalpha }
        , HNode{ variable=rvr, alpha=ralpha } ) =>
            Variable.eq(lvr,rvr) andalso lalpha = ralpha

      | ( _ , _ ) => false

  (* The hash value of a node is stored with it, because we can't
     use the address of the reference (like in C). Thus, it has to
     be computed by functions who construct SDD nodes. *)
  fun hash (iSDD(_,h,_)) = h

  fun configure UnicityTableConfiguration.Name =
    UnicityTableConfiguration.NameRes "SDD"
  |   configure UnicityTableConfiguration.Buckets =
    UnicityTableConfiguration.BucketsRes 2000000

end (* end struct Definition *)
open Definition

(*--------------------------------------------------------------------------*)
type SDD = Definition.t ref
datatype valuation = Nested of SDD | Values of values

(*--------------------------------------------------------------------------*)
structure SDDUT = UnicityTableFunID( structure Data = Definition )
structure H  = Hash
structure HT = HashTable

(*--------------------------------------------------------------------------*)
exception IncompatibleSDD
exception IsNotANode
exception IsNotValues
exception IsNotNested

(*--------------------------------------------------------------------------*)
(* Export an SDD to a string *)
fun toString (ref (iSDD(sdd,_,_))) =
let
  fun nodeHelper vlToString vr alpha =
   "(" ^ (Variable.toString vr) ^ ")" ^ " [ " ^
   (String.concatWith " + "
       (Util.VectorToList (Vector.map
        (fn (vl,succ) => (vlToString vl) ^ " --> "  ^ (toString succ))
        alpha )
       )
   ) ^ " ]"
in
  case sdd of
    Zero  => "|0|"
  | One   => "|1|"
  | Node{ variable=vr, alpha=alpha}  =>
      (nodeHelper Values.storedToString vr alpha)
  | HNode{ variable=vr, alpha=alpha} =>
      (nodeHelper toString vr alpha)
end

(*--------------------------------------------------------------------------*)
(* Extract the identifier of an SDD *)
fun uid (ref(iSDD(_,_,x))) = x

(*--------------------------------------------------------------------------*)
fun lt (x,y) = uid x < uid y

(*--------------------------------------------------------------------------*)
(* Help construct sorted operands of SDDs *)
fun insert [] x = [x]
|   insert (L as (l::ls)) x =
  if x = l then
    L
  else if uid x < uid l then
    x::L
  else
    l::insert ls x

(*--------------------------------------------------------------------------*)
(* Called by the unicity table to construct an SDD with an id *)
fun mkNode node hsh uid = iSDD( node, hsh, uid )

(*--------------------------------------------------------------------------*)
(* Return the |0| ("zero") terminal *)
val zero = SDDUT.unify (mkNode Zero (H.const 0))

(*--------------------------------------------------------------------------*)
(* Return the |1| ("one") terminal *)
val one = SDDUT.unify (mkNode One (H.const 1))

(*--------------------------------------------------------------------------*)
fun hashNode vlHash var alpha =
let
  val hsh =
    Vector.foldl (fn ( ( vl, succ), acc ) =>
                   H.hashCombine( acc
                                , H.hashCombine( vlHash vl, hash (!succ) )
                                )
                 )
                 (H.const 0)
                 alpha
in
  H.hashCombine( Variable.hash var, hsh)
end

(*--------------------------------------------------------------------------*)
(* Return a node with a set of discrete values on arc *)
fun flatNode ( var, values, rnext as (ref (iSDD(next,_,_))) ) =
  case ( Values.storedEmpty values , next ) of
    (_,Zero) => zero
  | (true,_) => zero
  | _        =>
    let
      val alpha = Vector.fromList [( values, rnext )]
      val hsh = hashNode Values.storedHash var alpha
    in
      SDDUT.unify ( mkNode (Node{ variable=var, alpha=alpha}) hsh )
    end

(*--------------------------------------------------------------------------*)
(* Construct a flat node with an pre-computed alpha. Internal use only! *)
fun flatNodeAlpha ( var, alpha ) =
  if Vector.length alpha = 0 then
    zero
  else
  let
    val hsh = hashNode Values.storedHash var alpha
  in
    SDDUT.unify ( mkNode (Node{variable=var,alpha=alpha}) hsh )
  end

(*--------------------------------------------------------------------------*)
(* Return an hierarchical node. Not exported *)
fun hierNode ( var, rnested as (ref (iSDD(nested,_,_)))
                  , rnext as (ref (iSDD(next,_,_)))
             )
= case ( next, nested ) of
    ( Zero , _ ) => zero
  | ( _ , Zero ) => zero
  | ( _ , _ )    =>
    let
      val alpha = Vector.fromList [( rnested, rnext )]
      val hsh = hashNode (hash o !) var alpha
    in
      SDDUT.unify ( mkNode (HNode{ variable=var, alpha=alpha}) hsh )
    end

(*--------------------------------------------------------------------------*)
(* Construct a node with an pre-computed alpha. Internal use only! *)
fun hierNodeAlpha ( var , alpha ) =
  if Vector.length alpha = 0 then
    zero
  else
  let
    val hsh = hashNode (hash o !) var alpha
  in
    SDDUT.unify ( mkNode (HNode{variable=var,alpha=alpha}) hsh )
  end

(*--------------------------------------------------------------------------*)
(* Return a node *)
fun node ( vr , vl , next ) =
  case vl of
    Values values => flatNode( vr, Values.mkStorable values, next )
  | Nested nested => hierNode( vr, nested, next )

(*--------------------------------------------------------------------------*)
val fromList = foldr (fn ((vr,vl),acc) => node( vr, vl, acc)) one

(*--------------------------------------------------------------------------*)
local (* SDD manipulation *)

(*--------------------------------------------------------------------*)
(* Operations to manipulate SDD. Used by the cache. *)
structure SDDOperations (* : OPERATION *) = struct

(*--------------------------------------------------------------------------*)
fun configure CacheConfiguration.Name =
  CacheConfiguration.NameRes "SDD"

(*--------------------------------------------------------------------------*)
(* Types required by the OPERATION signature *)
type result        = SDD
datatype operation = Union of
                        ( SDD list * (operation -> result) )
                   | Inter of
                        ( SDD list * (operation -> result) )
                   | Diff  of
                        ( SDD * SDD * (operation -> result) )

(*--------------------------------------------------------------------------*)
(* Check compatibility of operands *)
fun checkCompatibilty []     = raise DoNotPanic
|   checkCompatibilty(x::xs) =

  foldl (fn ( ref (iSDD(sx,_,_)), y as (ref (iSDD(sy,_,_)))) =>
        case (sx,sy) of
            (Zero,_)  => raise DoNotPanic
          | (_,Zero)  => raise DoNotPanic
          | (One,One) => y
          | (Node{variable=var1,...},Node{variable=var2,...}) =>
              if not( Variable.eq( var1, var2 ) ) then
                raise IncompatibleSDD
              else
                 y
          | (HNode{variable=var1,...},HNode{variable=var2,...}) =>
              if not( Variable.eq( var1, var2 ) ) then
                raise IncompatibleSDD
              else
                y
          | (_,_) => raise IncompatibleSDD
        )
        x
        xs

(*--------------------------------------------------------------------------*)
(* Convert an alpha (a vector) into a more easy to manipulate type
   (a list of values, each one leading to a list of successors).
   Thus, it makes it usable by squareUnion. *)
fun alphaToList( alpha ) =
  Vector.foldr
    (fn (x,acc) => let val (vl,succ) = x in (vl,[succ])::acc end )
    []
    alpha

(*--------------------------------------------------------------------------*)
(* Apply alphaToList to a node: SDD -> ( storedValues * SDD list ) list
   Warning! Duplicate logic with alphaNodeToList! *)
fun flatAlphaNodeToList n =
  case !n of
    iSDD(Node{alpha=alpha,...},_,_) => alphaToList alpha
  | _ => raise DoNotPanic

(*--------------------------------------------------------------------------*)
(* Apply alphaToList to a node: SDD -> ( SDD * SDD list ) list
   Warning! Duplicate logic with flatAlphaNodeToList! *)
fun alphaNodeToList n =
  case !n of
    iSDD(HNode{alpha=alpha,...},_,_) => alphaToList alpha
  | _ => raise DoNotPanic

(*--------------------------------------------------------------------------*)
(* Warning: duplicate with SDD.union! Operands should be sorted by caller. *)
fun unionCallback lookup xs =
  case List.filter (fn x => x <> zero ) xs of
    []     => zero   (* No need to cache *)
  | x::[]  => x      (* No need to cache *)
  | xs'    => lookup(Union( xs', lookup ))

(*--------------------------------------------------------------------------*)
(* Warning: duplicate with SDD.intersection!
   Operands should be sorted by caller. *)
fun intersectionCallback _      [] = zero
|   intersectionCallback _ (x::[]) = x
|   intersectionCallback lookup xs = lookup(Inter( xs, lookup))

(*--------------------------------------------------------------------------*)
(* Warning: duplicate with SDD.intersection! *)
fun differenceCallback lookup ( x, y ) =
  if x = y then          (* No need to cache *)
    zero
  else if x = zero then  (* No need to cache *)
    zero
  else if y = zero then  (* No need to cache *)
    x
  else
    lookup(Diff( x, y, lookup ))

(*--------------------------------------------------------------------------*)
fun union cacheLookup xs =
let
  val _ = checkCompatibilty xs
in
  case let val ref(iSDD(x,_,_)) = hd xs in x end of

  (* All operands are |1| *)
    One        => one

  (* There shouldn't be any |0|, they should have been filtered *)
  | Zero       => raise DoNotPanic

  (* Flat node case *)
  | Node{variable=var,...}  =>
    if Values.discrete then
    let
      val xs' = map flatAlphaNodeToList xs
    in
      flatNodeAlpha
      ( var
      , unionFlatDiscreteSDD Values.storedToList Values.storedFromList
                             Values.storedLt
                             Values.valueLt
                             uid
                             (unionCallback cacheLookup)
                             xs'
      )
    end
    else
    let
      val xs' = map flatAlphaNodeToList xs
      val squareUnion' = squareUnion uid
                                     (unionCallback cacheLookup)
                                     Values.storedUnion
                                     Values.storedLt
    in
      flatNodeAlpha
      ( var
      , squareUnion' (unionSDD uid
                               Values.storedIntersection
                               Values.storedDifference
                               Values.storedEmpty
                               xs'
                     )
      )
    end

  (* Hierarchical node case *)
  | HNode{variable=var,...} =>
  let
    val xs' = map alphaNodeToList xs
    val squareUnion' = squareUnion uid
                                   (unionCallback cacheLookup)
                                   (unionCallback cacheLookup)
                                   lt
  in
    hierNodeAlpha
    ( var
    , squareUnion' (unionSDD uid
                             (intersectionCallback cacheLookup)
                             (differenceCallback cacheLookup)
                             (fn x => x = zero)
                             xs'
                   )
    )
  end

end (* end fun union *)

(*--------------------------------------------------------------------------*)
(* N-ary intersection of SDDs *)
fun intersection cacheLookup xs =
let
  val hasZero = case List.find (fn x => x = zero ) xs of
                  NONE    => false
                | SOME _  => true
in
  (* Intersection of anything with |0| is always |0| *)
  if hasZero then
    zero
  else
    case let val ref(iSDD(x,_,_)) = hd xs in x end of

  (* All operands are |1| *)
    One        => checkCompatibilty xs

  (* There shouldn't be any |0| *)
  | Zero       => raise DoNotPanic

  | Node{variable=var,...}  =>
    let
      val _ = checkCompatibilty xs

      val ( initial, operands ) = case map flatAlphaNodeToList xs of
                                    []     => raise DoNotPanic
                                  | y::ys  => (y,ys)

      val commonApply' = commonApply Values.storedIntersection
                                     Values.storedEmpty
                                     (intersectionCallback cacheLookup)
                                     zero

      val squareUnion' = squareUnion uid
                                     (unionCallback cacheLookup)
                                     Values.storedUnion
                                     Values.storedLt
    in
      flatNodeAlpha( var
                   , squareUnion'( foldl commonApply' initial operands ) )
    end (* Flat node case *)

  | HNode{variable=var,...}  =>
    let
      val _ = checkCompatibilty xs

      val ( initial, operands ) = case map alphaNodeToList xs of
                                    []     => raise DoNotPanic
                                  | y::ys  => (y,ys)

      val commonApply' = commonApply (intersectionCallback cacheLookup)
                                     (fn x => x = zero )
                                     (intersectionCallback cacheLookup)
                                     zero

      val squareUnion' = squareUnion uid
                                     (unionCallback cacheLookup)
                                     (unionCallback cacheLookup)
                                     lt
    in
      hierNodeAlpha( var
                   , squareUnion' ( foldl commonApply' initial operands ) )
    end (* Hierachical node case *)
end (* end fun intersection *)

(*--------------------------------------------------------------------------*)
(* Compute the difference of two SDDs *)
fun difference cacheLookup ( ref (iSDD(l,_,_)), ref (iSDD(r,_,_)) ) =
let
  fun nodeDifference lvr rvr la ra
                     vlUnion vlInter vlDiff vlEmpty vlLt hierNodeAlpha
  =
    if not( Variable.eq(lvr,rvr) ) then
      raise IncompatibleSDD
    else
    let

      val lalpha = alphaToList la
      val ralpha = alphaToList ra

      val commonPart =
      let
        (* Difference is a binary operation, while commonApply
           expects an n-ary operation *)
        fun callback xs =
          case xs of
            x::y::[] => differenceCallback cacheLookup (x, y)
          | _        => raise DoNotPanic

        val commonApply' = commonApply vlInter
                                       vlEmpty
                                       callback
                                       zero
      in
        commonApply' ( lalpha, ralpha )
      end

      val diffPart =
      let
        val bUnion = vlUnion (map #1 ralpha)
      in
        foldl (fn ((aVal,aSuccs),acc) =>
                let
                  val diff = vlDiff(aVal,bUnion)
                in
                  if vlEmpty diff then
                    acc
                  else
                    ( diff, aSuccs)::acc
                end
              )
              []
              lalpha
      end

      val squareUnion' = squareUnion uid
                                     (unionCallback cacheLookup)
                                     vlUnion
                                     vlLt

      val alpha = squareUnion' ( diffPart @ commonPart )
    in
      hierNodeAlpha( lvr, alpha )
    end

in
  case (l,r) of

    (Zero,_)  => raise DoNotPanic
  | (_,Zero)  => raise DoNotPanic
  | (One,One) => raise DoNotPanic
  | (One,_  ) => raise IncompatibleSDD

  | ( Node{variable=lvr,alpha=la}, Node{variable=rvr,alpha=ra} ) =>
    nodeDifference lvr rvr la ra
                   Values.storedUnion Values.storedIntersection
                   Values.storedDifference
                   Values.storedEmpty Values.storedLt
                   flatNodeAlpha

  | ( HNode{variable=lvr,alpha=la}, HNode{variable=rvr,alpha=ra} ) =>
    nodeDifference lvr rvr la ra
                   (unionCallback cacheLookup)
                   (intersectionCallback cacheLookup)
                   (differenceCallback cacheLookup)
                   (fn x => x = zero) lt
                   hierNodeAlpha

  | ( Node{...}, _ ) => raise IncompatibleSDD
  | ( HNode{...}, _ ) => raise IncompatibleSDD


end (* end fun difference *)

(*--------------------------------------------------------------------------*)
(* Apply an SDD operation. Called by CacheFun. *)
fun apply (Union( xs, cacheLookup))  = union        cacheLookup xs
|   apply (Inter( xs, cacheLookup))  = intersection cacheLookup xs
|   apply (Diff( x,y, cacheLookup))  = difference   cacheLookup (x,y)

(*--------------------------------------------------------------------------*)
(* Hash an SDD operation *)
fun hash x =
let
  fun hashOperands( h0, xs ) =
    foldl (fn(x,h) => H.hashCombine( Definition.hash(!x), h)) h0 xs
in
  case x of
    Union(xs,_)  => hashOperands( H.const 15411567, xs)
  | Inter(xs,_ ) => hashOperands( H.const 78995947, xs)
  | Diff(l,r,_)  => H.hashCombine( H.const 94169137
                                 , H.hashCombine( Definition.hash(!l)
                                                , Definition.hash(!r) ) )
end

(*--------------------------------------------------------------------------*)
(* Compare two SDD operations *)
fun eq (x,y) =
  case (x,y) of
    ( Union(xs,_), Union(ys,_) )     => xs = ys
  | ( Inter(xs,_), Inter(ys,_) )     => xs = ys
  | ( Diff(lx,ly,_), Diff(rx,ry,_) ) => lx = rx andalso ly = ry
  | ( _, _ )                         => false

(*--------------------------------------------------------------------------*)
end (* end struct SDDOperations *)

(*--------------------------------------------------------------------------*)
in (* local SDD manipulations *)

(*--------------------------------------------------------------------------*)
(* Cache of operations on SDDs *)
structure SDDOpCache = CacheFun( structure Operation = SDDOperations )

(*--------------------------------------------------------------------------*)
(* Let operations in Op call the cache *)
val cacheLookup = SDDOpCache.lookup

(*--------------------------------------------------------------------------*)
(* Warning! Duplicate with SDD.SDDOperations.unionCallback!
   Operands should be sorted by caller. *)
fun union xs =
  case List.filter (fn x => x <> zero ) xs of
    []    => zero (* No need to cache *)
  | x::[] => x    (* No need to cache *)
  | xs'   => SDDOpCache.lookup(SDDOperations.Union( xs', cacheLookup ))

(*--------------------------------------------------------------------------*)
(* Warning! Duplicate with SDD.SDDOperations.intersectionCallback!
   Operands should be sorted by caller. *)
fun intersection []      = zero
|   intersection (x::[]) = x
|   intersection xs = SDDOpCache.lookup(SDDOperations.Inter(xs,cacheLookup))

(*--------------------------------------------------------------------------*)
(* Warning! Duplicate with SDD.SDDOperations.differenceCallback! *)
fun difference(x,y) =
 if x = y then          (* No need to cache *)
   zero
 else if x = zero then  (* No need to cache *)
   zero
 else if y = zero then  (* No need to cache *)
   x
 else
   SDDOpCache.lookup(SDDOperations.Diff( x, y, cacheLookup ))

(*--------------------------------------------------------------------------*)
end (* local SDD manipulations *)

(*--------------------------------------------------------------------------*)
fun nodeAlpha ( _ , []    ) = zero
|   nodeAlpha ( vr, alpha ) =
  case hd alpha of
    (Values _, _) =>
    let
      val squareUnion' = squareUnion uid union
                                     Values.storedUnion Values.storedLt
      val alpha' =
        List.mapPartial (fn ( Values v, succ ) =>
                          if Values.empty v orelse succ = zero then
                            NONE
                          else
                            SOME ( Values.mkStorable v, [succ] )
                        |   ( Nested _, _ ) =>
                          raise (Fail "Nested in a flat node")
                        )
                        alpha
    in
      flatNodeAlpha( vr, squareUnion' alpha' )
    end
  | (Nested _, _) =>
    let
      val squareUnion' = squareUnion uid union union lt
      val alpha' =
        List.mapPartial (fn ( Nested n, succ ) =>
                          if n = zero orelse succ = zero then
                            NONE
                          else
                            SOME ( n, [succ] )
                        |   ( Values _, _ ) =>
                          raise (Fail "Values in an hierarchical node")
                        )
                        alpha
    in
      hierNodeAlpha( vr, squareUnion' alpha' )
    end

(*--------------------------------------------------------------------------*)
(* Return the variable of an SDD. Needed by HomFun*)
fun variable (ref (iSDD(x,_,_))) =
  case x of
    Node{variable=var,...}  => var
  | HNode{variable=var,...} => var
  | _                       => raise IsNotANode

(*--------------------------------------------------------------------------*)
fun values x = case x of Nested _ => raise IsNotNested
                       | Values v => v

(*--------------------------------------------------------------------------*)
fun nested x = case x of Values _ => raise IsNotValues
                       | Nested s => s

(*--------------------------------------------------------------------------*)
fun alpha (ref (iSDD(sdd,_,_))) =
let
  fun alphaHelper a f =
      Vector.foldr
      (fn (x,acc) => let val (vl,succ) = x in (f vl,succ)::acc end )
      []
      a
in
  case sdd of
    Node{alpha=a,...}  => alphaHelper a (fn x => Values (Values.mkUsable x))
  | HNode{alpha=a,...} => alphaHelper a (fn x => Nested x)
  | _                  => raise IsNotANode
end

(*--------------------------------------------------------------------------*)
(* Return the hash value of an SDD. Needed by HomFun *)
val hash = Definition.hash o !

(*--------------------------------------------------------------------------*)
(* Return the hash value of a valuation. Needed by HomFun *)
fun hashValuation (Nested(ref n)) = Definition.hash n
|   hashValuation (Values(v))     = Values.hash v

(*--------------------------------------------------------------------------*)
(* Compare two valuations. Needed by HomFun *)
fun eqValuation (x,y) =
  case (x,y) of ( Nested nx, Nested ny ) => nx = ny
              | ( Values vx, Values vy ) => Values.eq( vx, vy )
              | ( _ , _ )                  => false

(*--------------------------------------------------------------------------*)
(* Export a valuation to a string. Needed by HomFun *)
fun valuationToString (Nested n) = toString n
|   valuationToString (Values v) = Values.toString v

(*--------------------------------------------------------------------------*)
type 'a visitor =    (unit -> 'a)
                  -> (unit -> 'a)
                  -> (int -> variable -> (valuation * SDD) list -> 'a)
                  -> SDD
                  -> 'a

(*--------------------------------------------------------------------------*)
datatype 'a visitorMode  = Cached | NonCached | Once of 'a

(*--------------------------------------------------------------------------*)
fun mkVisitor (mode:'a visitorMode) : 'a visitor =
let

  fun visitorBase zero one node s =
  let
    val ref(iSDD(x,_,uid)) = s
  in
    case x of
      Zero                      => zero ()
    | One                       => one ()
    | Node  {variable=v,...}  => node uid v (alpha s)
    | HNode {variable=v,...}  => node uid v (alpha s)
  end

in
    case mode of

      NonCached => visitorBase

    | Cached =>
      let
        val cache : (( SDD, 'a ) HT.hash_table)
            = ( HT.mkTable( fn x => hash x , op = )
                          ( 10000, DoNotPanic ) )

        fun visitorCache cache zero one node s =
          case HT.find cache s of
            NONE  =>
              let
                val res = visitorBase zero one node s
              in
              (
                HT.insert cache ( s, res );
                res
              )
              end
          | SOME v => v
      in
        visitorCache cache
      end

    | Once (neutral:'a) =>
      let
        val cache : (( SDD, unit ) HT.hash_table)
            = ( HT.mkTable( fn x => hash x , op = )
                          ( 10000, DoNotPanic ) )

        fun visitorOnce cache zero one node s =
          case HT.find cache s of
            NONE  =>
              (
                HT.insert cache ( s, () );
                visitorBase zero one node s
              )
          | SOME _ => neutral
      in
        visitorOnce cache
      end
end

(*--------------------------------------------------------------------------*)
fun stats () = SDDOpCache.stats()

(*--------------------------------------------------------------------------*)
end (* end functor SDDFun *)
