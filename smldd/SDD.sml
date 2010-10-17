(*--------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------*)

signature SDD =
sig

  eqtype SDD
  type variable
  type values
  eqtype values'

  datatype valuation    = Nested of SDD
                        | Values of values

  val zero              : SDD
  val one               : SDD
  val node              : variable * valuation * SDD -> SDD

  val union             : SDD list -> SDD
  val intersection      : SDD list -> SDD
  val difference        : SDD * SDD -> SDD

  val variable          : SDD -> variable
  val alpha             : SDD -> (valuation * SDD) list
  val hash              : SDD -> Hash.t

  val values            : valuation -> values
  val nested            : valuation -> SDD
  val hashValuation     : valuation -> Hash.t
  val eqValuation       : (valuation * valuation) -> bool
  val valuationToString : valuation -> string

  val nbPaths           : SDD -> IntInf.int

  val toString          : SDD -> string

  datatype dotMode      = ShowSharing | ShowHierarchy
  val toDot             : dotMode -> SDD -> string

  val stats             : unit -> string

  exception IncompatibleSDD
  exception NotYetImplemented
  exception IsNotANode
  exception IsNotValues
  exception IsNotNested

end

(*--------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------*)

functor SDDFun ( structure Variable  : VARIABLE
               ; structure Values    : VALUES )
  : SDD
= struct

  type variable   = Variable.t
  type values     = Values.plain
  type values'    = Values.unique

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  (* Define an SDD *)
  structure Definition =
  struct

    datatype t    = iSDD of ( sdd * Hash.t * int )
    and sdd       = Zero
                  | One
                  | Node of  { variable : variable
                             , alpha : (values' * t ref) Vector.vector
                             }
                  | HNode of { variable : variable
                             , alpha : ( t ref * t ref ) Vector.vector
                             }

    (* Compare two SDDs.
       At this point, we can't use the identifier to know if two SDDs are
       equals because this equality is called by the unicity table which is
       responsible for the generation of this id.=
    *)
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

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  type SDD = Definition.t ref

  datatype valuation = Nested of SDD | Values of values

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  (* Unicity *)
  structure SDDUT = UnicityTableFunID( structure Data = Definition )

  structure H  = Hash
  structure HT = HashTable

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  exception IncompatibleSDD
  exception NotYetImplemented
  exception IsNotANode
  exception IsNotValues
  exception IsNotNested

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  (* Export an SDD to a string *)
  fun toString (ref (iSDD(sdd,_,h))) =
  case sdd of
    Zero  => "|0|"
  | One   => "|1|"
  | Node{ variable=vr, alpha=alpha} =>
      "(" ^ (Variable.toString vr) ^ ")"
    (*^ " #" ^ (H.toString h) ^ "#"*)
    ^ " [ "
    ^ String.concatWith " + "
                        (VectorToList
                        (Vector.map (fn (values,succ) =>
                                      (Values.toString values)
                                    ^ " --> "
                                    ^ (toString succ)
                                    )
                                    alpha
                        ))
    ^ " ]"
  | HNode{ variable=vr, alpha=alpha} =>
    (Variable.toString vr)
    ^ " [ "
    ^ String.concatWith " + "
                        (VectorToList
                        (Vector.map (fn (nested,succ) =>
                                      (toString nested)
                                    ^ " --> "
                                    ^ (toString succ)
                                    )
                                    alpha
                        ))
    ^ " ]"

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)
  (* Extract the identifier of an SDD *)
  fun uid (ref(iSDD(_,_,x))) = x

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)
  (* Called by the unicity table to construct an SDD with an id *)
  fun mkNode n h uid = iSDD( n, h, uid)

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)
  (* Return the |0| ("zero") terminal *)
  val zero = SDDUT.unify (mkNode Zero (H.const 0))

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)
  (* Return the |1| ("one") terminal *)
  val one = SDDUT.unify (mkNode One (H.const 1))

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)
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

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)
  (* Construct a flat node with an already computed alpha.
     For internal use only! *)
  fun flatNodeAlpha ( var   : Variable.t
                    , alpha : (values' * SDD ) Vector.vector )
  =
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

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)
  (* Return an hierarchical node *)
  fun hierNode ( vr, rnested as (ref (iSDD(nested,hashNested,_)))
                   , rnext as (ref (iSDD(next,hashNext,_))) ) =
  case next of
    Zero => zero
  | _    =>
  ( case nested of
      Zero => zero
    | _    =>
      let
        val h = H.hashCombine( Variable.hash vr
                             , H.hashCombine( hashNext, hashNested ) )
        val alpha = Vector.fromList [( rnested, rnext )]
      in
        SDDUT.unify ( mkNode (HNode{ variable=vr, alpha=alpha}) h )
      end
  )

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)
  (* Construct a node with an already computed alpha.
     For internal use only! *)
  fun nodeAlpha ( vr : Variable.t , alpha : (SDD * SDD) Vector.vector )
  = if Vector.length alpha = 0 then
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

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)
  (* Return a node *)
  fun node ( vr : Variable.t, vl : valuation , next : SDD ) =
  case vl of
    Values(values) => flatNode( vr, Values.mkUnique values, next )
  | Nested(nested) => hierNode( vr, nested,           next )


  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  local (* SDD manipulation *)

    (*--------------------------------------------------------------------*)
    (*--------------------------------------------------------------------*)
    val sortSDDs = sortUnique uid (op <) (op >)

    (*--------------------------------------------------------------------*)
    (*--------------------------------------------------------------------*)
    (* Operations to manipulate SDD. Used by the cache. *)
    structure SDDOperations (* : OPERATION *) =
    struct

      val name = "SDD"

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)
      (* Types required by the OPERATION signature *)
      type result        = SDD
      datatype operation = Union of
                              ( SDD list * (operation -> result) )
                         | Inter of
                              ( SDD list * (operation -> result) )
                         | Diff  of
                              ( SDD * SDD * (operation -> result) )

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)
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

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)
      (* Convert an alpha (a vector) into a more easy to manipulate type
         (a list of values, each one leading to a list of successors).
         Thus, it make usable by squareUnion.

         (values * SDD) Vector.vector
           -> ( values * SDD list ) list

      *)
      fun alphaToList( alpha ) =
      Vector.foldr
        (fn (x,acc) => let val (vl,succ) = x in (vl,[succ])::acc end )
        []
        alpha

      (* Apply alphaToList to a node

         SDD
           -> ( values * SDD list ) list

         Warning! Duplicate logic with alphaNodeToList!
      *)
      fun flatAlphaNodeToList n =
      case !n of
        iSDD(Node{alpha=alpha,...},_,_) => alphaToList alpha
      | _ => raise DoNotPanic

      (* Apply alphaToList to a node

         SDD
           -> ( SDD * SDD list ) list

         Warning! Duplicate logic with flatAlphaNodeToList!
      *)
      fun alphaNodeToList n =
      case !n of
        iSDD(HNode{alpha=alpha,...},_,_) => alphaToList alpha
      | _ => raise DoNotPanic

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)
      (* Warning: duplicate code with SDD.union! Keep in sync! *)
      fun unionCallback lookup xs =
      let
        (* Remove all |0| *)
        val xs' = List.filter (fn x => case !x of
                                        iSDD(Zero,_,_) => false
                                      | _              => true
                              )
                              xs
      in
        case xs' of
          []      => zero   (* No need to cache *)
        | (x::[]) => x      (* No need to cache *)
        | _       => lookup(Union( sortSDDs xs', lookup ))
      end

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)
      (* Warning: duplicate code with SDD.intersection! Keep in sync! *)
      fun intersectionCallback lookup xs =
        case xs of
          []      => zero (* No need to cache *)
        | (x::[]) => x    (* No need to cache *)
        | _       => lookup(Inter( sortSDDs xs, lookup))

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)
      (* Warning: duplicate code with SDD.intersection! Keep in sync! *)
      fun differenceCallback lookup ( x, y ) =
        if x = y then          (* No need to cache *)
          zero
        else if x = zero then  (* No need to cache *)
          zero
        else if y = zero then  (* No need to cache *)
          x
        else
          lookup(Diff( x, y, lookup ))

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)
      (* Used by the intersection and difference operations which need
         to apply an operation ('cont') recursively on common parts.

          Warning! Duplicate logic with commonApply!
      *)
      fun flatCommonApply _ _         ( [], _ )                = []
      |   flatCommonApply lookup cont ( aArc::aAlpha, bAlpha ) =
      let

        fun propagate ( _, [] ) =  []
        |   propagate ( aArc as (aVal,aSuccs), (bVal,bSuccs)::bAlpha ) =
        let
          val inter = Values.intersection [aVal,bVal]
        in
          if Values.empty inter then
            propagate ( aArc, bAlpha)
          else
            let
              val succ = cont lookup (aSuccs@bSuccs)
            in
              if succ = zero then
                propagate ( aArc, bAlpha )
              else
                ( inter, [succ] ) :: propagate ( aArc, bAlpha)
            end
        end

      in
          propagate ( aArc, bAlpha  )
        @ flatCommonApply lookup cont ( aAlpha, bAlpha )
      end

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)
      (* Used by the intersection and difference operations which need
         to apply an operation ('cont') recursively on common parts.

         Warning! Duplicate logic with flatCommonApply!
      *)
      fun commonApply _ _         ( [], _ )                = []
      |   commonApply lookup cont ( aArc::aAlpha, bAlpha ) =
      let

        fun propagate ( _, [] ) =  []
        |   propagate ( aArc as (aVal,aSuccs), (bVal,bSuccs)::bAlpha ) =
        let
          val inter = intersectionCallback lookup [aVal,bVal]
        in
          if inter = zero then
            propagate ( aArc, bAlpha)
          else
            let
              val succ = cont lookup (aSuccs@bSuccs)
            in
              if succ = zero then
                propagate ( aArc, bAlpha )
              else
                ( inter, [succ] ) :: propagate ( aArc, bAlpha)
            end
        end

      in
          propagate ( aArc, bAlpha  )
        @ commonApply lookup cont ( aAlpha, bAlpha )
      end

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)
      (* Do the n-ary union of a list of flat SDDs.
         The general idea is to create a potential alpha
         of type (values * SDD list ) list which stores all
         successors for a given values set, which is then given to
         the square union function.

         In fact, it's not a real n-ary union as we operate on two operands
         at a time, the result becoming the 'bAlpha' operand on next iteration
         while 'aAlpha' is the head of the remaining operands (thus we use a 
         foldl). 'bAlpha' is initialized by the alpha of the first operand.
      *)
      fun union cacheLookup xs =
      let
        (* Check operands compatibility *)
        val _ = check xs
      in

        case let val ref(iSDD(x,_,_)) = hd xs in x end of

        (* All operands are |1| *)
          One        => one

        (* There shouldn't be any |0|, they should have been filtered
           before querying the cache.
        *)
        | Zero       => raise DoNotPanic

        (* Flat node case *)
        | Node{variable=var,...}  =>
          unionSDD flatAlphaNodeToList
                   alphaToList
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
                   alphaToList
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

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)
      (* N-ary intersection of SDDs *)
      fun intersection cacheLookup xs =
      let

        (* Test if there are any zero in operands *)
        val hasZero = case List.find (fn x => case !x of
                                                iSDD(Zero,_,_) => true
                                              | _              => false
                                     )
                                     xs
                       of
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
             (values,SDD list) list.
             This type is also used as the accumulator for the foldl
             on the list of operands, as it will be given to the
             square union operation.

             initial  : (values * SDD list) list
             operands : (values * SDD list) list list
          *)
          val ( initial, operands ) = case map flatAlphaNodeToList xs of
                                        []       => raise DoNotPanic
                                      | (y::ys)  => (y,ys)

          val flatCommonApply'
            = flatCommonApply cacheLookup intersectionCallback

          val squareUnion' = squareUnion uid
                                         (unionCallback cacheLookup)
                                         Values.union
                                         Values.lt

          (* Intersect two operands *)
          fun interHelper (xs,ys) = flatCommonApply'( xs, ys )

          val alpha = squareUnion' ( foldl interHelper initial operands )

        in
          flatNodeAlpha( var, alpha )
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
             operands : (SDD * SDD list) list list
          *)
          val ( initial, operands ) = case map alphaNodeToList xs of
                                        []       => raise DoNotPanic
                                      | (y::ys)  => (y,ys)

          val commonApply'
            = commonApply cacheLookup intersectionCallback

          val squareUnion' = squareUnion uid (unionCallback cacheLookup)
                                             (unionCallback cacheLookup)
                                             (fn (x,y) => uid x < uid y)

          (* Intersect two operands *)
          fun interHelper (xs,ys) = commonApply'( xs, ys )

          val alpha = squareUnion' ( foldl interHelper initial operands )

        in
          nodeAlpha( var, alpha )
        end (* Hierachical node case *)

      end (* end fun intersection *)

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)
      (* Compute the difference of two SDDs *)
      fun difference cacheLookup ( ref (iSDD(l,_,_)), ref (iSDD(r,_,_)) ) =
      case l of

        Zero => raise DoNotPanic

      | One  => (case r of
                  Zero => raise DoNotPanic
                | One  => zero
                | _           => raise IncompatibleSDD
                )

      | Node{variable=lvr,alpha=la} =>

      (case r of
        Zero       => raise DoNotPanic
      | One        => raise IncompatibleSDD
      | HNode{...} => raise IncompatibleSDD

      (* Difference of two flat nodes *)
      | Node{variable=rvr,alpha=ra} =>
      if not( Variable.eq(lvr,rvr) ) then
        raise IncompatibleSDD
      else
      let

        val lalpha = alphaToList la
        val ralpha = alphaToList ra

        val commonPart =
        let
          (* Difference is a binary operation, while flatCommonApply
             expects an n-ary operation *)
          fun callback lookup xs =
            case xs of
              (x::y::[]) => differenceCallback cacheLookup (x, y)
            | _          => raise DoNotPanic

          val flatCommonApply' = flatCommonApply cacheLookup callback
        in
          flatCommonApply'( lalpha, ralpha )
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
      )

      (* Difference of two hierarchical nodes *)
      | HNode{variable=lvr,alpha=la} =>

      (case r of
        Zero       => raise DoNotPanic
      | One        => raise IncompatibleSDD
      | Node{...}  => raise IncompatibleSDD

      (* Difference of two hiearchical nodes *)
      | HNode{variable=rvr,alpha=ra} =>
      if not( Variable.eq(lvr,rvr) ) then
        raise IncompatibleSDD
      else
      let

        val lalpha = alphaToList la
        val ralpha = alphaToList ra

        val commonPart =
        let
          (* Difference is a binary operation, while flatCommonApply
             expects an n-ary operation *)
          fun callback lookup xs =
            case xs of
              (x::y::[]) => differenceCallback cacheLookup (x, y)
            | _          => raise DoNotPanic

          val commonApply' = commonApply cacheLookup callback
        in
          commonApply'( lalpha, ralpha )
        end

        val diffPart =
        let
          val bUnion = unionCallback cacheLookup  (map (fn (x,_)=>x) ralpha)
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
      )

      (* end fun difference *)

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)
      (* Apply an SDD operation. Called by CacheFun. *)
      fun apply x =
      case x of
        Union( xs, cacheLookup)  => union        cacheLookup xs
      | Inter( xs, cacheLookup)  => intersection cacheLookup xs
      | Diff( x,y, cacheLookup)  => difference   cacheLookup (x,y)

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)
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

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)
      (* Compare two SDD operations *)
      fun eq (x,y) =
        case (x,y) of
          ( Union(xs,_), Union(ys,_) )     => xs = ys
        | ( Inter(xs,_), Inter(ys,_) )     => xs = ys
        | ( Diff(lx,ly,_), Diff(rx,ry,_) ) => lx = rx andalso ly = ry
        | ( _, _ )                         => false

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

    end (* end struct SDDOperations *)

  in (* local SDD manipulations *)

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)
    (* Cache of operations on SDDs *)
    structure SDDOpCache = CacheFun( structure Operation = SDDOperations )

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)

    (* Let operations in Op call the cache *)
    val cacheLookup = SDDOpCache.lookup

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)
    (* Warning! Duplicate code with SDD.SDDOperations.unionCallback! *)
    fun union xs =
    let
      (* Remove all |0| *)
      val xs' = List.filter (fn x => case !x of
                                       iSDD(Zero,_,_) => false
                                     | _              => true
                            )
                            xs
    in
      case xs' of
        []      => zero (* No need to cache *)
      | (x::[]) => x    (* No need to cache *)
      | _       => SDDOpCache.lookup(SDDOperations.Union( sortSDDs xs'
                                                        , cacheLookup ))
    end

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)

    (* Warning! Duplicate code with SDD.SDDOperations.intersectionCallback! *)
    fun intersection xs =
    case xs of
      []      => zero (* No need to cache *)
    | (x::[]) => x    (* No need to cache *)
    | _       => SDDOpCache.lookup(SDDOperations.Inter( sortSDDs xs
                                                      , cacheLookup ))

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)

    (* Warning! Duplicate code with SDD.SDDOperations.differenceCallback! *)
    fun difference(x,y) =
    if x = y then          (* No need to cache *)
      zero
    else if x = zero then  (* No need to cache *)
      zero
    else if y = zero then  (* No need to cache *)
      x
    else
      SDDOpCache.lookup(SDDOperations.Diff( x, y, cacheLookup ))

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)

  end (* local SDD manipulations *)

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)
  (* Return the variable of an SDD. Needed by HomFun*)
  fun variable (ref (iSDD(x,_,_))) =
  case x of
    Node{variable=var,...}  => var
  | HNode{variable=var,...} => var
  | _                       => raise IsNotANode

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)
  fun values x = case x of
                   Nested _ => raise IsNotNested
                 | Values v => v

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)
  fun nested x = case x of
                   Values v => raise IsNotValues
                 | Nested s => s

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)
  fun alpha (x as (ref (iSDD(sdd,_,_)))) =
  let
    fun alphaHelper a f =
        Vector.foldr
        (fn (x,acc) => let val (vl,succ) = x in (f vl,succ)::acc end )
        []
        a
  in
    case sdd of
      Node{alpha=a,...}  => alphaHelper a (fn x => Values (Values.mkPlain x))
    | HNode{alpha=a,...} => alphaHelper a (fn x => Nested x)
    | _                  => raise IsNotANode
  end

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)
  (* Return the hash value of an SDD. Needed by HomFun*)
  fun hash x = Definition.hash (!x)

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)
  (* Return the hash value of a valuation. Needed by HomFun*)
  fun hashValuation x =
  case x of
    Nested(nested) => Definition.hash (!nested)
  | Values(values) => Values.hash (Values.mkUnique values)

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)
  (* Compare two valuations. Needed by HomFun*)
  fun eqValuation (x,y) =
  case (x,y) of
    ( Nested(nx), Nested(ny) ) => nx = ny
  | ( Values(vx), Values(vy) ) => (Values.mkUnique vx) = (Values.mkUnique vy)
  | ( _ , _ )                  => false

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)
  (* Export a valuation to a string. Needed by HomFun*)
  fun valuationToString x =
  case x of
    Nested(nested) => toString nested
  | Values(values) => Values.toString (Values.mkUnique values)

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)
  (* Count the number of distinct paths in an SDD *)
  fun nbPaths x =
    let
      val cache : (( SDD, IntInf.int ) HT.hash_table) ref
          = ref ( HT.mkTable( fn x => hash x , op = )
                           ( 10000, DoNotPanic ) )
      fun pathsHelper x =
        let
          val iSDD(sdd,_,_) = !x
        in
            case sdd of
            Zero  =>  IntInf.fromInt 0
          | One   =>  IntInf.fromInt 1
          | Node{alpha=(arcs),...} =>
              (case HT.find (!cache) x of
                SOME r => r
              | NONE   =>
                let
                  val value = Vector.foldl
                                    ( fn ((v,succ), n ) =>
                                      n
                                      +
                                      (
                                        IntInf.fromInt(Values.length v)
                                      * pathsHelper succ
                                      )
                                    )
                                    0
                                    arcs
                  val _     = HT.insert (!cache) ( x, value )
                in
                  value
                end
              )

          | HNode{alpha=(arcs),...} =>
              (case HT.find (!cache) x of
                SOME r => r
              | NONE   =>
                let
                  val value = Vector.foldl
                                    ( fn ((v,succ), n ) =>
                                      n
                                      +
                                      (
                                        pathsHelper v
                                      * pathsHelper succ
                                      )
                                    )
                                    0
                                    arcs
                  val _     = HT.insert (!cache) ( x, value )
                in
                  value
                end
              )
        end
    in
      pathsHelper x
    end (* end fun paths *)

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)
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
        "\"node"
      ^ (Int.toString (uid sdd))
      ^ (depthStr depth)
      ^ "\" [shape=circle,label=\""
      ^ (Variable.toString (variable sdd))
      ^ "\"];\n"
      ^ (foldl (fn ((_,succ),str) => str ^ (dotHelper succ depth))
               ""
               (alpha sdd)
        )

    fun hNode sdd depth dotHelper =
        "\"node"
      ^ (Int.toString (uid sdd))
      ^ (depthStr depth)
      ^ "\" [shape=circle,label=\""
      ^ (Variable.toString (variable sdd))
      ^ "\"];\n"
      ^ (foldl (fn ((nested,succ),str) =>
                  str
                ^ (dotHelper (case nested of
                               Values _ => raise DoNotPanic
                             | Nested n => n
                             )
                             (depth +1)
                  )
                ^ (dotHelper succ depth)
               )
               ""
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
                  (* Insert only for the first time, as
                     in real sharing mode, we don't care
                     about depth
                  *)
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
      | _ => ""
    end

    fun nodeArc sdd depth =
      foldl (fn((values,succ),str) =>
                str
              ^ "\"node"
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
                | Values v => Values.toString (Values.mkUnique v)
                )
              ^ "\"];\n"
             )
             ""
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
              ^ ghost ^ " [shape=point,label=\"\",height=0,width=0];\n"
              ^ curr  ^ " -> " ^ ghost ^ " [arrowhead=none];\n"
              ^ ghost ^ " -> " ^ nxt ^ ";\n"
              ^ ghost ^ " -> " ^ nst ^ " [style=dashed,weight=0];\n"
            end
            )
            ""
            (alpha sdd)

    fun dotArcHelper () =
      HT.foldi (fn (sdd, ref depths, str) =>
                 str ^
                 (case let val ref(iSDD(s,_,_)) = sdd in s end of
                    Node{...} =>
                      foldl (fn (depth,str) => str ^ (nodeArc sdd depth))
                            ""
                            depths
                  | HNode{...} =>
                      foldl (fn (depth,str) => str ^ (hNodeArc sdd depth))
                            ""
                            depths
                  | _ => ""
                  )
               )
               ""
               nodes

   in
     if x = one then
      terminal 1 0
     else if x = zero then
      terminal 0 0
     else
      "digraph sdd {\n\n"
    ^ (dotHelper x 0)
    ^ (dotArcHelper ())
    ^ (if maxShare then
         terminal 1 0
       else
         String.concat (List.tabulate ( !maxDepth + 1, terminal 1) )
      )
    ^ "\n}\n"
   end (* fun toDot *)

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)
  fun stats () =
   SDDOpCache.stats()

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

end (* end functor SDDFun *)

(*--------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------*)

structure SDD = SDDFun( structure Variable  = IntVariable
                      ; structure Values    = DiscreteIntValues )

(*structure BoolSDD = SDDFun( structure Variable  = IntVariable
                          ; structure Values    = BooleanValues )*)


(*--------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------*)
