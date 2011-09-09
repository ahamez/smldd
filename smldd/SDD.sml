(*--------------------------------------------------------------------------*)
signature SDD = sig

  type SDD
  type variable
  type values

  (* An SDD node holds a valuation on all arcs going to its successors. A
     valuation can be a nested SDD or a set of values (at the deepest level
     of the hierarchy). *)
  datatype valuation      = Nested of SDD
                          | Values of values

  (* Return the |0| terminal. *)
  val zero                : SDD
  (* Return the |1| terminal. *)
  val one                 : SDD
  (* Create an SDD variable {valuation} -> successor. *)
  val node                : variable * valuation * SDD -> SDD
  (* Create an SDD from an alpha (associative list of valuation * SDD). *)
  val nodeAlpha           : variable * (valuation * SDD) list -> SDD
  (* Create an SDD from a sequence of (variable * valuation). *)
  val fromList            : (variable * valuation ) list -> SDD

  (* Perform the union of a list of SDDs. Raise IncompatibleSDD if two or more
     SDDs in the list are incompatible. *)
  val union               : SDD list -> SDD
  (* Perform the intersection of a list of SDDs. Raise IncompatibleSDD if two
     or more SDDs in the list are incompatible.*)
  val intersection        : SDD list -> SDD
  (* Perform the difference of two SDDs. Raise IncompatibleSDD if the two SDDs
     are incompatible.*)
  val difference          : SDD * SDD -> SDD
  (* Tell if an SDD is the empty set. Same as x = |0| *)
  val empty               : SDD -> bool
  (* Tell if two SDDs are equals. Constant time. *)
  val eq                  : SDD * SDD -> bool
  (* Compare two SDDs. Constant time. *)
  val lt                  : SDD * SDD -> bool
  (* Return the unique identifier of an SDD. Warning, uids are recycled! *)
  val uid                 : SDD -> int
  (* Return the variable of an SDD. Raise IsNotANode if it's a terminal. *)
  val variable            : SDD -> variable
  (* Return the alpha function of an SDD as an associative list.
     Raise IsNotANode if the given SDD is a terminal. *)
  val alpha               : SDD -> (valuation * SDD) list
  (* Retrurn the hash value of an SDD. *)
  val hash                : SDD -> Hash.t
  (* Export an SDD to a string. Do not use on big SDDs. *)
  val toString            : SDD -> string

  (* Helper function to insert an SDD in a sorted list. *)
  val insert              : SDD list -> SDD -> SDD list
  (* Helper function to sort a list of SDDs. *)
  val sort                : SDD list -> SDD list

  (* Return the values of a valuation. Raise IsNotValues if the valuation is
     a nested SDD. *)
  val values              : valuation -> values
  (* Return the nested SDD of a valuation. Raise IsNotNested if the valuation is
     not a nested SDD. *)
  val nested              : valuation -> SDD
  (* Return the hash value of a valuation. *)
  val hashValuation       : valuation -> Hash.t
  (* Tell if two valuations are equals. Constant time if both valuations are
     nested SDDs. Otherwise, it depends on the compare function of values. *)
  val eqValuation         : (valuation * valuation) -> bool
  (* Export a valuation to a string. *)
  val valuationToString   : valuation -> string

  (* The possible modes of an SDD visitor:
       - Cached    : store (all) results of the visitation
       - NonCached : do not cache results of visitation.
       - Once      : visit only once each node
  *)
  datatype 'a visitorMode = Cached | NonCached | Once of 'a
  (* The type of the visitor funcion. A visitor is created by mkVisitor.
     Then, the visitor must be given the the functions described below.
     *)
  type 'a visitor         =  (* |0| terminal visited, provided by user *)
                             (unit -> 'a)
                             (* |1| terminal visited, provided by user *)
                          -> (unit -> 'a)
                             (* An SDD node visited, provided by user *)
                          -> (int -> variable -> (valuation * SDD) list -> 'a)
                             (* The SDD to visit *)
                          -> SDD
                             (* The result of the visitation*)
                          -> 'a
  (* Create a visitor on a SDD *)
  val mkVisitor           : 'a visitorMode -> 'a visitor

  (* Export some statistics to string *)
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
structure H  = Hash

(*--------------------------------------------------------------------------*)
(* Define an SDD *)
structure Definition (* : DATA *) = struct

  datatype sdd = Zero
               | One
               | Node  of { variable : variable
                          , alpha : (storedValues * t) Vector.vector
                          }
               | HNode of { variable : variable
                          , alpha : (t * t) Vector.vector
                          }
  withtype t = (sdd * int)

  (* Compare two SDDs.
     At this point, we can't use the identifier to know if two SDDs are
     equals because this equality is called by the unicity table which is
     responsible for the generation of this id.= *)
  fun eq ( (lsdd,_), (rsdd,_) ) =
    case ( lsdd, rsdd ) of

        ( Zero, Zero ) => true
      | ( One, One   ) => true

      | ( Node{ variable=lvr, alpha=lalpha }
        , Node{ variable=rvr, alpha=ralpha } ) =>
            Variable.eq(lvr,rvr) andalso
            let
              fun loop i =
              if i = Vector.length lalpha then
                true
              else
              let
                val ( lvl, (_,luid) ) = Vector.sub( lalpha, i)
                val ( rvl, (_,ruid) ) = Vector.sub( ralpha, i)
              in
                if Values.storedEq(lvl,rvl) andalso luid = ruid then
                  loop (i+1)
                else
                  false
              end
            in
              if Vector.length lalpha <> Vector.length ralpha then
                false
              else
                loop 0
            end

      | ( HNode{ variable=lvr, alpha=lalpha }
        , HNode{ variable=rvr, alpha=ralpha } ) =>
            Variable.eq(lvr,rvr) andalso
            let
              fun loop 0 = true
              |   loop i =
              let
                val ( (_,lvluid), (_,luid) ) =
                  Vector.sub( lalpha, i - 1)
                val ( (_,rvluid), (_,ruid) ) =
                  Vector.sub( ralpha, i - 1)
              in
                if lvluid = rvluid andalso luid = ruid then
                  loop (i-1)
                else
                  false
              end
            in
              if Vector.length lalpha <> Vector.length ralpha then
                false
              else
                loop (Vector.length lalpha)
            end

      | ( _ , _ ) => false

  fun hash (sdd,_) =
    case sdd of
      Zero => H.hashInt 0
    | One  => H.hashInt 1
    | Node{ variable=var, alpha=alpha } =>
    let
      val hsh =
        Vector.foldl (fn ( ( vl, (_,uid)), acc ) =>
                       H.hashCombine( acc
                                    , H.hashCombine( Values.storedHash vl
                                                   , H.hashInt uid
                                                   )
                                    )
                     )
                     (H.hashInt 9289317)
                     alpha
    in
      H.hashCombine( Variable.hash var, hsh)
    end
    | HNode{ variable=var, alpha=alpha } =>
    let
      val hsh =
        Vector.foldl (fn ( ( (_,vluid), (_,succuid) ) , acc ) =>
                       H.hashCombine( acc
                                    , H.hashCombine( H.hashInt vluid
                                                   , H.hashInt succuid
                                                   )
                                    )
                     )
                     (H.hashInt 3984921)
                     alpha
    in
      H.hashCombine( Variable.hash var, hsh)
    end

  fun configure UnicityTableConfiguration.Name =
    UnicityTableConfiguration.NameRes "SDD"
  |   configure UnicityTableConfiguration.Buckets =
    UnicityTableConfiguration.BucketsRes 2000000

end (* end struct Definition *)
open Definition

(*--------------------------------------------------------------------------*)
type SDD = Definition.t
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
fun toString (sdd,_) =
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
fun uid (_, x) = x
fun eq (x, y)  = uid x = uid y
fun lt (x, y)  = uid x < uid y

(*--------------------------------------------------------------------------*)
(* Help construct sorted operands of SDDs *)
fun insert ls x =
let
  fun helper acc [] x = x::acc
  |   helper acc (L as (l::ls)) x =
    if eq(x, l) then
      L@acc
    else if lt(x, l) then
      x::L@acc
    else
      helper (l::acc) ls x
in
  helper [] ls x
end

(*--------------------------------------------------------------------------*)
(* Insert sort is sufficient as lists to sort are often small enough *)
fun sort [] = []
|   sort xs = foldr (fn (x,acc) => insert acc x) [] xs

(*--------------------------------------------------------------------------*)
(* Called by the unicity table to construct an SDD with an id *)
fun mkNode node uid = (node, uid)

(*--------------------------------------------------------------------------*)
(* Return the |0| ("zero") terminal *)
val zero = SDDUT.unify (mkNode Zero)

(*--------------------------------------------------------------------------*)
(* Return the |1| ("one") terminal *)
val one = SDDUT.unify (mkNode One)

(*--------------------------------------------------------------------------*)
(* An SDD is empty if it's |0|. By contruction, all SDDs terminated by |0|
   are reduced to |0|. *)
fun empty x = eq(x, zero)

(*--------------------------------------------------------------------------*)
(* Return a node with a set of discrete values on arc *)
fun flatNode ( var, values, rnext as (next,_) ) =
  case ( Values.storedEmpty values , next ) of
    (_,Zero) => zero
  | (true,_) => zero
  | _        =>
    let
      val alpha = Vector.fromList [( values, rnext )]
    in
      SDDUT.unify ( mkNode (Node{ variable=var, alpha=alpha}) )
    end

(*--------------------------------------------------------------------------*)
(* Construct a flat node with an pre-computed alpha. Internal use only! *)
fun flatNodeAlpha ( var, alpha ) =
  if Vector.length alpha = 0 then
    zero
  else
    SDDUT.unify ( mkNode (Node{variable=var,alpha=alpha}) )

(*--------------------------------------------------------------------------*)
(* Return an hierarchical node. Not exported *)
fun hierNode ( var, rnested as (nested,_) , rnext as (next,_) ) =
  case ( next, nested ) of
      ( Zero , _ ) => zero
    | ( _ , Zero ) => zero
    | ( _ , _ )    =>
      let
        val alpha = Vector.fromList [( rnested, rnext )]
      in
        SDDUT.unify ( mkNode (HNode{ variable=var, alpha=alpha}) )
      end

(*--------------------------------------------------------------------------*)
(* Construct a node with an pre-computed alpha. Internal use only! *)
fun hierNodeAlpha ( var , alpha ) =
  if Vector.length alpha = 0 then
    zero
  else
    SDDUT.unify ( mkNode (HNode{variable=var,alpha=alpha}) )

(*--------------------------------------------------------------------------*)
(* Return a node *)
fun node ( vr , vl , next ) =
  case vl of
    Values values => flatNode( vr, Values.mkStorable values, next )
  | Nested nested => hierNode( vr, nested, next )

(*--------------------------------------------------------------------------*)
val fromList = foldr (fn ((vr,vl),acc) => node( vr, vl, acc)) one

(*--------------------------------------------------------------------------*)
val hash = H.hashInt o uid

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
datatype operation = Union of ( SDD list * (operation -> result)  )
                   | Inter of ( SDD list * (operation -> result)  )
                   | Diff  of ( SDD * SDD * (operation -> result) )

(*--------------------------------------------------------------------------*)
(* Check compatibility of operands *)
fun checkCompatibility []      = raise DoNotPanic
|   checkCompatibility (x::xs) =

  foldl (fn ( (sx,_), y as (sy,_) ) =>
        case (sx,sy) of
            (* All |0| shhould have been filtered before calling the cache *)
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
fun alphaToList alpha =
  Vector.foldr (fn ((vl, succ), acc) => (vl, [succ])::acc) [] alpha

(*--------------------------------------------------------------------------*)
(* Apply alphaToList to a node: SDD -> (storedValues * SDD list) list
   Warning! Duplicate logic with alphaNodeToList! *)
fun flatAlphaNodeToList (Node{alpha=alpha, ...}, _) = alphaToList alpha
|   flatAlphaNodeToList _                           = raise DoNotPanic

(*--------------------------------------------------------------------------*)
(* Apply alphaToList to a node: SDD -> (SDD * SDD list) list
   Warning! Duplicate logic with flatAlphaNodeToList! *)
fun alphaNodeToList (HNode{alpha=alpha,...}, _) = alphaToList alpha
|   alphaNodeToList _                           = raise DoNotPanic

(*--------------------------------------------------------------------------*)
(* Warning: duplicate with SDD.union! Operands should be sorted by caller. *)
fun unionCallback lookup xs =
  case List.filter (not o empty) xs of
    []  => zero   (* No need to cache *)
  | [x] => x      (* No need to cache *)
  | xs' => lookup(Union( xs', lookup ))

(*--------------------------------------------------------------------------*)
(* Warning: duplicate with SDD.intersection!
   Operands should be sorted by caller. *)
fun intersectionCallback _      [] = zero
|   intersectionCallback _     [x] = x
|   intersectionCallback lookup xs =
  case List.find empty xs of
    NONE   => lookup(Inter( xs, lookup))
  | SOME _ => zero

(*--------------------------------------------------------------------------*)
(* Warning: duplicate with SDD.intersection! *)
fun differenceCallback lookup (x, y) =
  if eq(x, y) then    (* No need to cache *)
    zero
  else if empty x then  (* No need to cache *)
    zero
  else if empty y then  (* No need to cache *)
    x
  else
    lookup(Diff(x, y, lookup))

(*--------------------------------------------------------------------------*)
fun union cacheLookup xs =
let
  (* Raise IncompatibleSDD *)
  val _ = checkCompatibility xs
in
  case let val (x,_) = hd xs in x end of

  (* All operands are |1| *)
    One        => one

  (* There shouldn't be any |0|, they should have been removed before
     calling the cache. *)
  | Zero       => raise DoNotPanic

  (* Flat node case *)
  | Node{variable=var,...}  =>
    if Values.discrete then
    let
      val xs' = map flatAlphaNodeToList xs
    in
      flatNodeAlpha
      ( var
      , unionFlatDiscreteSDD Values.storedToList
                             Values.storedFromList
                             Values.storedEq
                             Values.storedLt
                             Values.valueLt
                             eq
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
                                     Values.storedEq
                                     Values.storedLt
    in
      flatNodeAlpha
      ( var
      , squareUnion' (unionSDD uid
                               Values.storedEq
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
                                   eq
                                   lt
  in
    hierNodeAlpha
    ( var
    , squareUnion' (unionSDD uid
                             eq
                             (intersectionCallback cacheLookup)
                             (differenceCallback cacheLookup)
                             empty
                             xs'
                   )
    )
  end

end (* end fun union *)

(*--------------------------------------------------------------------------*)
(* N-ary intersection of SDDs *)
fun intersection cacheLookup xs =
  case let val (x,_) = hd xs in x end of

  (* All operands are |1| *)
    One        => checkCompatibility xs

  (* There shouldn't be any |0| *)
  | Zero       => raise DoNotPanic

  | Node{variable=var,...}  =>
    let
      val _ = checkCompatibility xs

      val ( initial, operands ) = case map flatAlphaNodeToList xs of
                                    []     => raise DoNotPanic
                                  | y::ys  => (y,ys)

      val commonApply' = commonApply Values.storedIntersection
                                     Values.storedEmpty
                                     (intersectionCallback cacheLookup)
                                     empty

      val squareUnion' = squareUnion uid
                                     (unionCallback cacheLookup)
                                     Values.storedUnion
                                     Values.storedEq
                                     Values.storedLt
    in
      flatNodeAlpha( var
                   , squareUnion' (foldl commonApply' initial operands)
                   )
    end (* Flat node case *)

  | HNode{variable=var,...}  =>
    let
      (* Raise IncompatibleSDD *)
      val _ = checkCompatibility xs

      val ( initial, operands ) = case map alphaNodeToList xs of
                                    []     => raise DoNotPanic
                                  | y::ys  => (y,ys)

      val commonApply' = commonApply (intersectionCallback cacheLookup)
                                     empty
                                     (intersectionCallback cacheLookup)
                                     empty

      val squareUnion' = squareUnion uid
                                     (unionCallback cacheLookup)
                                     (unionCallback cacheLookup)
                                     eq
                                     lt
    in
      hierNodeAlpha( var
                   , squareUnion' (foldl commonApply' initial operands)
                   )
    end (* Hierachical node case *)

(* end fun intersection *)

(*--------------------------------------------------------------------------*)
(* Compute the difference of two SDDs *)
fun difference cacheLookup ((l,_), (r,_)) =
let
  (* Factorize the code for Node and HNode, the algorithm is the same, only
     callbacks change. *)
  fun nodeDifference lvr rvr la ra vlEq
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
        fun callback (x1::x2::_) =
          differenceCallback cacheLookup (x1, x2)

        val commonApply' = commonApply vlInter
                                       vlEmpty
                                       callback
                                       empty
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
                                     vlEq
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
                   Values.storedEq
                   Values.storedUnion
                   Values.storedIntersection
                   Values.storedDifference
                   Values.storedEmpty
                   Values.storedLt
                   flatNodeAlpha

  | ( HNode{variable=lvr,alpha=la}, HNode{variable=rvr,alpha=ra} ) =>
    nodeDifference lvr rvr la ra
                   eq
                   (unionCallback cacheLookup)
                   (intersectionCallback cacheLookup)
                   (differenceCallback cacheLookup)
                   empty
                   lt
                   hierNodeAlpha

  | ( Node{...}, _)  => raise IncompatibleSDD
  | ( HNode{...}, _) => raise IncompatibleSDD

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
  fun hashOperands(h0, xs) =
    foldl (fn ((_,uid), h) => H.hashCombine(H.hashInt uid, h)) h0 xs
in
  case x of
    Union(xs, _) => hashOperands(H.hashInt 15411567, xs)
  | Inter(xs, _) => hashOperands(H.hashInt 78995947, xs)
  | Diff((_, luid), (_, ruid), _) =>
      H.hashCombine( H.hashInt 94169137
                   , H.hashCombine( H.hashInt luid
                                  , H.hashInt ruid
                                  )
                   )
end

(*--------------------------------------------------------------------------*)
(* We need an alias for the equality of SDDs as the next eq will mask it. *)
val SDDeq = eq

(* Compare two SDD operations *)
fun eq (x,y) =
let
  fun helper [] [] = true
  |   helper [] _  = false
  |   helper _  [] = false
  |   helper (x::xs) (y::ys) =
    if SDDeq( x, y ) then
      helper xs ys
    else
      false
in
  case (x,y) of
    (Union(xs, _), Union(ys, _))       => helper xs ys
  | (Inter(xs, _), Inter(ys, _))       => helper xs ys
  | (Diff(lx, ly, _), Diff(rx, ry, _)) => SDDeq(lx,rx) andalso SDDeq(ly,ry)
  | (_, _)                         => false
end

(*--------------------------------------------------------------------------*)
end (* end struct SDDOperations *)

(*--------------------------------------------------------------------------*)
in (* local SDD manipulations *)

(*--------------------------------------------------------------------------*)
(* Cache of operations on SDDs *)
structure SDDOpCache = CacheFun(structure Operation = SDDOperations)

(*--------------------------------------------------------------------------*)
(* Let operations in Op call the cache *)
val cacheLookup = SDDOpCache.lookup

(*--------------------------------------------------------------------------*)
(* Warning! Duplicate with SDD.SDDOperations.unionCallback!
   Operands should be sorted by caller. *)
fun union xs =
  case List.filter (not o empty) xs of
    []  => zero (* No need to cache *)
  | [x] => x    (* No need to cache *)
  | xs' => SDDOpCache.lookup(SDDOperations.Union(xs', cacheLookup))

(*--------------------------------------------------------------------------*)
(* Warning! Duplicate with SDD.SDDOperations.intersectionCallback!
   Operands should be sorted by caller. *)
fun intersection []  = zero
|   intersection [x] = x
|   intersection xs  =
  case List.find empty xs of
    NONE   => SDDOpCache.lookup(SDDOperations.Inter(xs, cacheLookup))
  | SOME _ => zero

(*--------------------------------------------------------------------------*)
(* Warning! Duplicate with SDD.SDDOperations.differenceCallback! *)
fun difference (x, y) =
 if eq(x, y) then          (* No need to cache *)
   zero
 else if eq(x, zero) then  (* No need to cache *)
   zero
 else if eq(y, zero) then  (* No need to cache *)
   x
 else
   SDDOpCache.lookup(SDDOperations.Diff(x, y, cacheLookup))

(*--------------------------------------------------------------------------*)
end (* local SDD manipulations *)

(*--------------------------------------------------------------------------*)
fun nodeAlpha (_ , [])   = zero
|   nodeAlpha (vr, alpha) =
  case hd alpha of
    (Values _, _) =>
    let
      val squareUnion' =
        squareUnion
          uid union Values.storedUnion Values.storedEq Values.storedLt

      val alpha' =
        List.mapPartial (fn ( Values v, succ ) =>
                          if Values.empty v orelse empty succ then
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
      val squareUnion' = squareUnion uid union union eq lt
      val alpha' =
        List.mapPartial (fn (Nested n, succ) =>
                          if empty n orelse empty succ then
                            NONE
                          else
                            SOME ( n, [succ] )
                        |   (Values _, _) =>
                          raise (Fail "Values in an hierarchical node")
                        )
                        alpha
    in
      hierNodeAlpha( vr, squareUnion' alpha' )
    end

(*--------------------------------------------------------------------------*)
(* Return the variable of an SDD. Needed by HomFun*)
fun variable (Node{variable=var, ...}, _)  = var
|   variable (HNode{variable=var, ...}, _) = var
|   variable _                             = raise IsNotANode

(*--------------------------------------------------------------------------*)
fun values (Values v) = v
|   values (Nested _) = raise IsNotValues

(*--------------------------------------------------------------------------*)
fun nested (Values _) = raise IsNotNested
|   nested (Nested s) = s

(*--------------------------------------------------------------------------*)
fun alpha (sdd,_) =
let
  fun alphaHelper a f =
    Vector.foldr (fn ((vl, succ), acc) => (f vl,succ)::acc) [] a
in
  case sdd of
    Node{alpha=a,...}  => alphaHelper a (fn x => Values (Values.mkUsable x))
  | HNode{alpha=a,...} => alphaHelper a (fn x => Nested x)
  | _                  => raise IsNotANode
end

(*--------------------------------------------------------------------------*)
(* Return the hash value of a valuation. Needed by HomFun *)
fun hashValuation (Nested(_,uid)) = H.hashInt uid
|   hashValuation (Values v)      = Values.hash v

(*--------------------------------------------------------------------------*)
(* Compare two valuations. Needed by HomFun *)
fun eqValuation (Nested nx, Nested ny) = eq(nx, ny)
|   eqValuation (Values vx, Values vy) = Values.eq(vx, vy)
|   eqValuation (_, _)                 = false

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
    val (x,uid) = s
  in
    case x of
      Zero                    => zero ()
    | One                     => one ()
    | Node  {variable=v,...}  => node uid v (alpha s)
    | HNode {variable=v,...}  => node uid v (alpha s)
  end

in
    case mode of

      NonCached => visitorBase

    | Cached =>
      let
        val cache : ((SDD, 'a) HT.hash_table) =
          (HT.mkTable(fn x => hash x , eq) (10000, DoNotPanic))

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
        val cache : ((SDD, unit) HT.hash_table) =
          (HT.mkTable (fn x => hash x , eq) (10000, DoNotPanic))

        fun visitorOnce cache zero one node s =
          case HT.find cache s of
            NONE  =>
              (
                HT.insert cache (s, ());
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
