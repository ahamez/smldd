(*--------------------------------------------------------------------------*)
signature SDD = sig

  eqtype SDD
  type variable
  type userValues

  datatype valuation    = Nested of SDD
                        | Values of userValues

  val zero              : SDD
  val one               : SDD
  val node              : variable * valuation * SDD -> SDD

  val union             : SDD list -> SDD
  val intersection      : SDD list -> SDD
  val difference        : SDD * SDD -> SDD

  val variable          : SDD -> variable
  val alpha             : SDD -> (valuation * SDD) list
  val hash              : SDD -> Hash.t

  val insert            : SDD list -> SDD -> SDD list

  val values            : valuation -> userValues
  val nested            : valuation -> SDD
  val hashValuation     : valuation -> Hash.t
  val eqValuation       : (valuation * valuation) -> bool
  val valuationToString : valuation -> string

  val toString          : SDD -> string

  datatype dotMode      = ShowSharing | ShowHierarchy
  val toDot             : dotMode -> SDD -> string

  val stats             : unit -> string

  type 'a visitor       =    (unit -> 'a)
                          -> (unit -> 'a)
                          -> (variable -> (valuation * SDD) list -> 'a)
                          -> SDD
                          -> 'a
  val mkCachedVisitor   : 'a -> 'a visitor
  val visit             : 'a visitor

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
type userValues   = Values.user
type storedValues = Values.stored

(*--------------------------------------------------------------------------*)
(* Define an SDD *)
structure Definition = struct

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

end (* end struct Definition *)
open Definition

(*--------------------------------------------------------------------------*)
type SDD = Definition.t ref
datatype valuation = Nested of SDD | Values of userValues

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
fun toString (ref (iSDD(sdd,_,h))) =
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
  | Node{ variable=vr, alpha=alpha}  => (nodeHelper Values.toString vr alpha)
  | HNode{ variable=vr, alpha=alpha} => (nodeHelper toString vr alpha)
end

(*--------------------------------------------------------------------------*)
(* Extract the identifier of an SDD *)
fun uid (ref(iSDD(_,_,x))) = x

(*--------------------------------------------------------------------------*)
(* Help construct sorted operands of SDDs *)
fun insert [] x = [x]
|   insert (L as (l::ls)) x =
  if x = l then
    L
  else if uid x < uid l then
    x::L
  else
    l::(insert ls x)

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
(* Return a node with a set of discrete values on arc *)
fun flatNode ( var, values, rnext as (ref (iSDD(next,hashNext,_))) )
  = case next of
    Zero => zero
  | _    =>
    if Values.empty values then
      zero
    else
      let
        val hashValues = Values.hash values
        val h = H.hashCombine( Variable.hash var
                           , H.hashCombine( hashNext, hashValues ))
        val alpha = Vector.fromList [( values, rnext )]
      in
        SDDUT.unify ( mkNode (Node{ variable=var, alpha=alpha}) h )
      end

(*--------------------------------------------------------------------------*)
(* Construct a flat node with an pre-computed alpha. Internal use only! *)
fun flatNodeAlpha ( var, alpha ) =
  if Vector.length alpha = 0 then
    zero
  else
  let
    val hashAlpha = Vector.foldl (fn ((vl,succ),h) =>
                                    H.hashCombine( Values.hash vl
                                               , H.hashCombine( hash(!succ),h)
                                               )
                                  )
                     (H.const 0)
                     alpha

    val h = H.hashCombine( Variable.hash var, hashAlpha )
  in
    SDDUT.unify ( mkNode (Node{variable=var,alpha=alpha}) h )
  end

(*--------------------------------------------------------------------------*)
(* Return an hierarchical node. Not exported *)
fun hierNode ( vr, rnested as (ref (iSDD(nested,hashNested,_)))
                 , rnext as (ref (iSDD(next,hashNext,_))) )
= case ( next, nested ) of
    ( Zero , _ ) => zero
  | ( _ , Zero ) => zero
  | ( _ , _ )    =>
    let
      val h = H.hashCombine( Variable.hash vr
                           , H.hashCombine( hashNext, hashNested ) )
      val alpha = Vector.fromList [( rnested, rnext )]
    in
      SDDUT.unify ( mkNode (HNode{ variable=vr, alpha=alpha}) h )
    end

(*--------------------------------------------------------------------------*)
(* Construct a node with an pre-computed alpha. Internal use only! *)
fun nodeAlpha ( vr , alpha ) =
  if Vector.length alpha = 0 then
    zero
  else
  let
    val hashAlpha = Vector.foldl (fn ((vl,succ),h) =>
                                    H.hashCombine( hash (!vl)
                                               , H.hashCombine( hash(!succ),h)
                                               )
                                  )
                     (H.const 0)
                     alpha

    val h = H.hashCombine( Variable.hash vr, hashAlpha )
  in
    SDDUT.unify ( mkNode (HNode{variable=vr,alpha=alpha}) h )
  end

(*--------------------------------------------------------------------------*)
(* Return a node *)
fun node ( vr , vl , next ) =
  case vl of
    Values(values) => flatNode( vr, Values.mkStorable values, next )
  | Nested(nested) => hierNode( vr, nested,           next )

(*--------------------------------------------------------------------------*)
local (* SDD manipulation *)

(*--------------------------------------------------------------------*)
(* Operations to manipulate SDD. Used by the cache. *)
structure SDDOperations (* : OPERATION *) = struct

(*--------------------------------------------------------------------------*)
val name = "SDD"

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
fun check []     = raise DoNotPanic
|   check(x::xs) =

  foldl (fn (x as (ref (iSDD(sx,_,_))),y as (ref (iSDD(sy,_,_)))) =>
        case sx of
          (* Zero should have been filtered out *)
            Zero => raise DoNotPanic
          | One  => (case sy of
                      One => y
                    | _ => raise IncompatibleSDD
                    )

          | Node{variable=var1,...} =>
              (case sy of
                Node{variable=var2,...} =>
                  if not( Variable.eq( var1, var2 ) ) then
                    raise IncompatibleSDD
                  else
                    y
              | _ => raise IncompatibleSDD
              )

          | HNode{variable=var1,...} =>
              (case sy of
                HNode{variable=var2,...} =>
                  if not( Variable.eq( var1, var2 ) ) then
                    raise IncompatibleSDD
                  else
                    y
              | _ => raise IncompatibleSDD
              )
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
(* Warning: duplicate with SDD.union!
   Operands should be sorted by caller. *)
fun unionCallback lookup xs =
  case List.filter (fn x => x <> zero ) xs of
    []      => zero   (* No need to cache *)
  | (x::[]) => x      (* No need to cache *)
  | xs'     => lookup(Union( xs', lookup ))

(*--------------------------------------------------------------------------*)
(* Warning: duplicate with SDD.intersection!
   Operands should be sorted by caller. *)
fun intersectionCallback lookup xs =
  case xs of
    []      => zero (* No need to cache *)
  | (x::[]) => x    (* No need to cache *)
  | _       => lookup(Inter( xs, lookup))

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
  (* Check operands compatibility *)
  val _ = check xs
in
  case let val ref(iSDD(x,_,_)) = hd xs in x end of

  (* All operands are |1| *)
    One        => one

  (* There shouldn't be any |0|, they should have been filtered *)
  | Zero       => raise DoNotPanic

  (* Flat node case *)
  | Node{variable=var,...}  =>
    if Values.discrete then
      unionFlatDiscreteSDD flatAlphaNodeToList
                           Values.toList Values.fromList Values.lt
                           Values.valueLt
                           uid
                           (unionCallback cacheLookup)
                           flatNodeAlpha
                           xs var
    else
      unionSDD flatAlphaNodeToList
               uid
               (squareUnion uid
                            (unionCallback cacheLookup)
                            Values.union
                            Values.lt
               )
               Values.intersection
               Values.difference
               Values.empty
               flatNodeAlpha
               xs var

  (* Hierarchical node case *)
  | HNode{variable=var,...} =>
    unionSDD alphaNodeToList
             uid
             (squareUnion uid
                          (unionCallback cacheLookup)
                          (unionCallback cacheLookup)
                          (fn (x,y) => uid x < uid y)
             )
             (intersectionCallback cacheLookup)
             (differenceCallback cacheLookup)
             (fn x => x = zero)
             nodeAlpha
             xs var

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
    One        => check xs

  (* There shouldn't be any |0| *)
  | Zero       => raise DoNotPanic

  (* Flat node case *)
  | Node{variable=var,...}  =>
  let
    (* Check operands compatibility *)
    val _ = check xs

    (* Transform the alpha of each node into :
       (storedValues,SDD list) list.
       This type is also used as the accumulator for the foldl
       on the list of operands, as it will be given to the
       square union operation.

       initial  : (storedValues * SDD list) list
       operands : (storedValues * SDD list) list list *)
    val ( initial, operands ) = case map flatAlphaNodeToList xs of
                                  []       => raise DoNotPanic
                                | (y::ys)  => (y,ys)

    val commonApply' = commonApply Values.intersection
                                   Values.empty
                                   (intersectionCallback cacheLookup)
                                   zero

    val squareUnion' = squareUnion uid
                                   (unionCallback cacheLookup)
                                   Values.union
                                   Values.lt
  in
    flatNodeAlpha( var
                 , squareUnion'( foldl commonApply' initial operands ) )
  end (* Flat node case *)

  (* Hierachical node case *)
  | HNode{variable=var,...}  =>
  let
    (* Check operands compatibility *)
    val _ = check xs

    (* Transform the alpha of each node into :
       (SDD,SDD list) list.
       This type is also used as the accumulator for the foldl
       on the list of operands, as it will be given to the
       square union operation.

       initial  : (SDD * SDD list) list
       operands : (SDD * SDD list) list list *)
    val ( initial, operands ) = case map alphaNodeToList xs of
                                  []       => raise DoNotPanic
                                | (y::ys)  => (y,ys)

    val commonApply' = commonApply (intersectionCallback cacheLookup)
                                   (fn x => x = zero )
                                   (intersectionCallback cacheLookup)
                                   zero

    val squareUnion' = squareUnion uid
                                   (unionCallback cacheLookup)
                                   (unionCallback cacheLookup)
                                   (fn (x,y) => uid x < uid y)
  in
    nodeAlpha( var
             , squareUnion' ( foldl commonApply' initial operands ) )
  end (* Hierachical node case *)
end (* end fun intersection *)

(*--------------------------------------------------------------------------*)
(* Compute the difference of two SDDs *)
fun difference cacheLookup ( ref (iSDD(l,_,_)), ref (iSDD(r,_,_)) ) =
  case (l,r) of

    (Zero,_)  => raise DoNotPanic
  | (_,Zero)  => raise DoNotPanic
  | (One,One) => raise DoNotPanic
  | (One,_  ) => raise IncompatibleSDD

  | ( Node{variable=lvr,alpha=la}, Node{variable=rvr,alpha=ra} ) =>
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
            (x::y::[]) => differenceCallback cacheLookup (x, y)
          | _          => raise DoNotPanic

        val commonApply' = commonApply Values.intersection
                                       Values.empty
                                       callback
                                       zero
      in
        commonApply' ( lalpha, ralpha )
      end

      val diffPart =
      let
        val bUnion = Values.union( map (fn (x,_)=>x) ralpha )
      in
        foldl (fn ((aVal,aSuccs),acc) =>
                let
                  val diff = Values.difference(aVal,bUnion)
                in
                  if Values.empty diff then
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
                                     Values.union
                                     Values.lt

      val alpha = squareUnion' ( diffPart @ commonPart )
    in
      flatNodeAlpha( lvr, alpha )
    end

  | ( Node{...}, _ ) => raise IncompatibleSDD

  (* Difference of two hierarchical nodes *)
  | ( HNode{variable=lvr,alpha=la}, HNode{variable=rvr,alpha=ra} ) =>
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
            (x::y::[]) => differenceCallback cacheLookup (x, y)
          | _          => raise DoNotPanic

        val commonApply' = commonApply (intersectionCallback cacheLookup)
                                       (fn x => x = zero )
                                       callback
                                       zero
      in
        commonApply' ( lalpha, ralpha )
      end

      val diffPart =
      let
        val bUnion = unionCallback cacheLookup (map (fn (x,_)=>x) ralpha)
      in
        foldl (fn ((aVal,aSuccs),acc) =>
                let
                  val diff = differenceCallback cacheLookup (aVal,bUnion)
                in
                  if diff = zero then
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
                                     (unionCallback cacheLookup)
                                     (fn (x,y) => uid x < uid y)
      val alpha = squareUnion' ( diffPart @ commonPart )
    in
      nodeAlpha( lvr, alpha )
    end

  | ( HNode{...}, _ ) => raise IncompatibleSDD

  (* end fun difference *)

(*--------------------------------------------------------------------------*)
(* Apply an SDD operation. Called by CacheFun. *)
fun apply x =
  case x of
    Union( xs, cacheLookup)  => union        cacheLookup xs
  | Inter( xs, cacheLookup)  => intersection cacheLookup xs
  | Diff( x,y, cacheLookup)  => difference   cacheLookup (x,y)

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
                                            , Definition.hash(!r) )
                               )
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
    []      => zero (* No need to cache *)
  | (x::[]) => x    (* No need to cache *)
  | xs'     => SDDOpCache.lookup(SDDOperations.Union( xs', cacheLookup ))

(*--------------------------------------------------------------------------*)
(* Warning! Duplicate with SDD.SDDOperations.intersectionCallback!
   Operands should be sorted by caller. *)
fun intersection xs =
 case xs of
   []      => zero (* No need to cache *)
 | (x::[]) => x    (* No need to cache *)
 | _       => SDDOpCache.lookup(SDDOperations.Inter( xs, cacheLookup ))

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
fun nested x = case x of Values v => raise IsNotValues
                       | Nested s => s

(*--------------------------------------------------------------------------*)
fun alpha (x as (ref (iSDD(sdd,_,_)))) =
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
fun hash x = Definition.hash (!x)

(*--------------------------------------------------------------------------*)
(* Return the hash value of a valuation. Needed by HomFun *)
fun hashValuation x =
  case x of Nested(nested) => Definition.hash (!nested)
          | Values(values) => Values.hashUsable values

(*--------------------------------------------------------------------------*)
(* Compare two valuations. Needed by HomFun *)
fun eqValuation (x,y) =
  case (x,y) of ( Nested(nx), Nested(ny) ) => nx = ny
              | ( Values(vx), Values(vy) ) => Values.eqUsable( vx, vy )
              | ( _ , _ )                  => false

(*--------------------------------------------------------------------------*)
(* Export a valuation to a string. Needed by HomFun *)
fun valuationToString x =
 case x of Nested(nested) => toString nested
         | Values(values) => Values.toString (Values.mkStorable values)

(*--------------------------------------------------------------------------*)
type 'a visitor       =    (unit -> 'a)
                        -> (unit -> 'a)
                        -> (variable -> (valuation * SDD) list -> 'a)
                        -> SDD
                        -> 'a

(*--------------------------------------------------------------------------*)
fun visit zero one node s =
  case let val ref(iSDD(x,_,_)) = s in x end of
    Zero                        => zero ()
  | One                         => one ()
  | Node  {variable=v,alpha=a}  => node v (alpha s)
  | HNode {variable=v,alpha=a}  => node v (alpha s)

(*--------------------------------------------------------------------------*)
fun mkCachedVisitor (dummy : 'a) =
let

  val cache : (( SDD, 'a ) HT.hash_table) ref
      = ref ( HT.mkTable( fn x => hash x , op = )
                        ( 10000, DoNotPanic ) )

  fun visitor cache zero one node s =
    case HT.find (!cache) s of
      NONE  =>
        let
          val res = case let val ref(iSDD(x,_,_)) = s in x end of
                      Zero                        => zero ()
                    | One                         => one ()
                    | Node  {variable=v,alpha=a}  => node v (alpha s)
                    | HNode {variable=v,alpha=a}  => node v (alpha s)

        in
        (
          HT.insert (!cache) ( s, res );
          res
        )
        end
    | SOME v => v

in
  visitor cache
end
(*--------------------------------------------------------------------------*)
(* Indicate if the dot output emphasizes on hierarchy or sharing *)
datatype dotMode = ShowSharing | ShowHierarchy

(* Export an SDD to a DOT representation *)
fun toDot mode x =
let

  val maxShare = case mode of ShowHierarchy => false
                            | ShowSharing   => true

  fun depthStr depth = if maxShare then
                         ""
                       else
                         "_" ^ (Int.toString depth)

  fun terminal value depth =
      "terminal"
    ^ (Int.toString value)
    ^ (depthStr depth)
    ^ " [shape=rectangle,regular=true,label=\""
    ^ (Int.toString value)
    ^ "\"];\n"

  fun node sdd depth dotHelper =
    [ "\"node"
    ^ (Int.toString (uid sdd))
    ^ (depthStr depth)
    ^ "\" [shape=circle,label=\""
    ^ (Variable.toString (variable sdd))
    ^ "\"];\n"
    ]
    @ (foldl (fn ((_,succ),str) => str @ (dotHelper succ depth))
             []
             (alpha sdd)
      )

  fun hNode sdd depth dotHelper =
      "\"node"
    ^ (Int.toString (uid sdd))
    ^ (depthStr depth)
    ^ "\" [shape=circle,label=\""
    ^ (Variable.toString (variable sdd))
    ^ "\"];\n"
    :: (foldl (fn ((vl,succ),str) =>
                str
              @ (dotHelper (nested vl) (depth +1) )
              @ (dotHelper succ depth)
             )
             []
             (alpha sdd)
      )

  (* Associate an SDD to a list of all hierarchies it belongs to *)
  val nodes : ( ( SDD , int list ref ) HT.hash_table )
        = (HT.mkTable( fn x => hash x , op = ) ( 10000, DoNotPanic ))

  val maxDepth = ref 0

  fun dotHelper sdd depth =
  let
    val _ = case HT.find nodes sdd of
              NONE        => HT.insert nodes ( sdd, ref [depth] )
            | SOME depths =>
              if maxShare then
                (* Insert only for the first time, as in real sharing mode,
                   we don't care about depth *)
                ()
              else
              let
                fun insertSorted x [] = []
                |   insertSorted x (Y as (y::ys)) =
                  if x = y then
                    Y
                  else if x < y then
                    x::Y
                  else
                    y::(insertSorted x ys)
              in
                depths := insertSorted depth (!depths)
              end
    val _ = if depth > !maxDepth then
              maxDepth := depth
            else
              ()
  in
    case !sdd of
      iSDD(Node{...},_,_)  => node sdd depth dotHelper
    | iSDD(HNode{...},_,_) => hNode sdd depth dotHelper
    | _ => []
  end

  fun nodeArc sdd depth =
    foldl (fn((values,succ),str) =>
              str
            @ [ "\"node"
              ^ (Int.toString (uid sdd))
              ^ (depthStr depth)
              ^ "\""
              ^ " -> "
              ^ (case let val ref(iSDD(x,_,_)) = succ in x end of
                  Zero       => raise DoNotPanic
                | One        => "terminal1" ^ (depthStr depth)
                | Node{...}  => "\"node" ^ (Int.toString (uid succ))
                                       ^ (depthStr depth) ^ "\""
                | HNode{...} => "\"node" ^ (Int.toString (uid succ))
                                        ^ (depthStr depth) ^ "\""
                )
              ^ " [label=\""
              ^ (case values of
                  Nested _ => raise DoNotPanic
                | Values v => Values.toString (Values.mkStorable v)
                )
              ^ "\"];\n"
              ]
          )
          []
          (alpha sdd)

  fun hNodeArc sdd depth =
    foldl (fn((vl,succ),str) =>
          let
            val curr  =   "\"node"
                        ^ (Int.toString (uid sdd))
                        ^ (depthStr depth)
                        ^ "\""
            val ghost =   "\"ghost"
                        ^ (Int.toString(uid sdd))
                        ^ "_"
                        ^ (Int.toString(uid (nested vl)))
                        ^ "_"
                        ^ (Int.toString(uid succ))
                        ^ (depthStr depth)
                        ^ "\""
            val nst   =   "\"node"
                        ^ (Int.toString(uid (nested vl)))
                        ^ (depthStr (depth + 1))
                        ^ "\""
            val nxt   = (case let val ref(iSDD(x,_,_)) = succ in x end of
                          Zero       => raise DoNotPanic
                        | One        => "terminal1" ^ (depthStr depth)
                        | _          => "\"node" ^ (Int.toString (uid succ))
                                        ^ (depthStr depth) ^ "\""
                        )
          in
              str
            @ [ ghost ^ " [shape=point,label=\"\",height=0,width=0];\n"
              ^ curr  ^ " -> " ^ ghost ^ " [arrowhead=none];\n"
              ^ ghost ^ " -> " ^ nxt ^ ";\n"
              ^ ghost ^ " -> " ^ nst ^ " [style=dashed,weight=0];\n"
              ]
          end
          )
          []
          (alpha sdd)

  fun dotArcHelper () =
    HT.foldi (fn (sdd, ref depths, str) =>
               str @
               (case let val ref(iSDD(s,_,_)) = sdd in s end of
                  Node{...} =>
                    foldl (fn (depth,str) => str @ (nodeArc sdd depth))
                          []
                          depths
                | HNode{...} =>
                    foldl (fn (depth,str) => str @ (hNodeArc sdd depth))
                          []
                          depths
                | _ => []
                )
             )
             []
             nodes

  val l = if x = one then
            [terminal 1 0]
          else if x = zero then
            [terminal 0 0]
          else
              ["digraph sdd {\n\n"]
            @ (dotHelper x 0)
            @ (dotArcHelper ())
            @ (if maxShare then
                [terminal 1 0]
              else
                List.tabulate ( !maxDepth + 1, terminal 1)
              )
            @ ["\n}\n"]
  in
    String.concat l
  end (* fun toDot *)

(*--------------------------------------------------------------------------*)
fun stats () = SDDOpCache.stats()

(*--------------------------------------------------------------------------*)
end (* end functor SDDFun *)
