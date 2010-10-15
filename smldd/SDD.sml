(*--------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------*)

signature SDD =
sig

  eqtype SDD
  type variable
  type values

  datatype valuation    = Nested of SDD
                        | Values of values

  val zero              : SDD
  val one               : SDD
  val flatNode          : variable * values    * SDD -> SDD
  val node              : variable * valuation * SDD -> SDD

  val union             : SDD list -> SDD
  val intersection      : SDD list -> SDD
  val difference        : SDD * SDD -> SDD

  val variable          : SDD -> variable
  val alpha             : SDD -> (valuation * SDD) list
  val hash              : SDD -> Hash.t
  val hashValuation     : valuation -> Hash.t
  val eqValuation       : (valuation * valuation) -> bool
  val valuationToString : valuation -> string

  val paths             : SDD -> IntInf.int

  val toString          : SDD -> string
  val toDot             : SDD -> string

  val stats             : unit -> string

  exception IncompatibleSDD
  exception NotYetImplemented
  exception IsNotANode

end

(*--------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------*)

functor SDDFun ( structure Variable  : VARIABLE
               ; structure Values    : VALUES )
  : SDD
= struct

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  (* Define an SDD *)
  structure Definition =
  struct

    datatype t    = iSDD of ( sdd * Hash.t * int )
    and sdd       = Zero
                  | One
                  | Node of  { variable : Variable.t
                             , alpha : (Values.t ref * t ref) Vector.vector
                             }
                  | HNode of { variable : Variable.t
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
      case lsdd of

        Zero => (case rsdd of
                  Zero  => true
                | _     => false
                )

      | One  => (case rsdd of
                  One   => true
                | _     => false
                )

      | Node{ variable=lvr, alpha=lalpha } =>
          (case rsdd of
            Node{ variable=rvr, alpha=ralpha } =>
              if not( Variable.eq(lvr,rvr) ) then
                false
              else
                lalpha = ralpha
          | _ => false
          )

      | HNode{ variable=lvr, alpha=lalpha } =>
          (case rsdd of
            HNode{ variable=rvr, alpha=ralpha } =>
              if not( Variable.eq(lvr,rvr) ) then
                false
              else
                lalpha = ralpha
          | _ => false
          )

    (* end fun eq *)

    (* The hash value of a node is stored with it, because we can't
       use the address of the reference (like in C). Thus, it has to
       be computed by functions who construct SDD nodes. *)
    fun hash (iSDD(_,h,_)) = h

  end (* end struct Definition *)
  open Definition

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  type SDD        = Definition.t ref
  type variable   = Variable.t
  type values     = Values.t

  datatype valuation = Nested of SDD | Values of values

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  (* Unicity *)
  structure ValUT = UnicityTableFun  ( structure Data = Values )
  structure SDDUT = UnicityTableFunID( structure Data = Definition )

  structure H  = Hash
  structure HT = HashTable

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  exception IncompatibleSDD
  exception NotYetImplemented
  exception IsNotANode

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
                                      Values.toString(!values)
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

  (* Called by the unicity table to construct an SDD with an id *)
  fun mkNode n h id = iSDD( n, h, id)

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
          val unikValues = ValUT.unify values
          val alpha = Vector.fromList [( unikValues, rnext )]
        in
          SDDUT.unify ( mkNode (Node{ variable=var, alpha=alpha}) h )
        end

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  (* Construct a flat node with an already computed alpha.
     For internal use only! *)
  fun flatNodeAlpha ( var   : Variable.t
                    , alpha : (values ref * SDD ) Vector.vector )
  =
  if Vector.length alpha = 0 then
    zero
  else
  let
    val hashAlpha = Vector.foldl (fn ((vl,succ),h) =>
                                    H.hashCombine( Values.hash(!vl)
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
    Values(values) => flatNode( vr, values, next )
  | Nested(nested) => hierNode( vr, nested, next )

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  local (* Values manipulations *)

    (* Operations to manipulate values. Used by the cache. *)
    structure ValuesOperations (* : OPERATION *) =
    struct

      val name = "Values"

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

      type result        = values ref
      datatype operation = Union of values ref list
                         | Inter of values ref list
                         | Diff  of values ref * values ref

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

      fun eq (l,r) =
        case l of
          Union(xs) =>    (case r of
                            Union(ys) => xs = ys
                          |  _ => false
                          )
        | Inter(xs) =>    (case r of
                            Inter(ys) => xs = ys
                          | _ => false
                          )
        | Diff(lx,ly) =>  (case r of
                            Diff(rx,ry) => lx = rx andalso ly = ry
                          | _ => false
                          )

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

      fun hash x =
        let
          (* Values.hash(!x) -> problem: we have to compute again
             the hash value of the valuation... Maybe we should store
             this hash alongside of the valuation? *)
          fun hashOperands( h0, xs ) =
            foldl (fn(x,h) => H.hashCombine( Values.hash(!x), h)) h0 xs
        in
          case x of
            Union(xs) => hashOperands( H.const 15411567, xs)
          | Inter(xs) => hashOperands( H.const 78995947, xs)
          | Diff(l,r) => H.hashCombine( H.const 94165961
                                    , H.hashCombine( Values.hash(!l)
                                                 , Values.hash(!r))
                                    )
        end

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

      (* Evaluation an operation on valuations. Called by CacheFun. *)
      fun apply operation =

        case operation of

          Union []     => raise DoNotPanic
        | Union(x::xs) =>
            ValUT.unify(foldl ( fn (x,res) => Values.union(!x,res) )
                              (!x)
                              xs
                        )

        | Inter []     => raise DoNotPanic
        | Inter(x::xs) =>
            ValUT.unify(foldl ( fn (x,res) => Values.intersection(!x,res) )
                              (!x)
                              xs
                        )

        | Diff(x,y)    => ValUT.unify( Values.difference( !x, !y) )

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

    end (* end structure ValuesOperations *)

  in (* local values manipulations *)

    (* Cache of operations on valuess *)
    structure ValOpCache = CacheFun(structure Operation = ValuesOperations)

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)

    fun valUnion xs =
      case xs of
        []      => raise DoNotPanic
      | (x::[]) => x (* No need to cache *)
      | _       => ValOpCache.lookup( ValuesOperations.Union(xs) )

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)

    fun valIntersection xs =
      case xs of
        []      => raise DoNotPanic
      | (x::[]) => x (* No need to cache *)
      | _       => ValOpCache.lookup( ValuesOperations.Inter(xs) )

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)

    fun valDifference(x,y) =
      if x = y then
        ValUT.unify( Values.mkEmpty() )
      else
        ValOpCache.lookup( ValuesOperations.Diff(x,y) )

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)

    val stats = ValOpCache.stats

  end (* local valuess manipulations *)

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  local (* SDD manipulation *)

    (* Sort operands of union and intersection, using their hash values *)
    fun qsort []       = []
    |   qsort (x::xs)  =
    let
      fun id x = let val iSDD(_,_,id) = !x in id end
      val (left,right) = List.partition (fn y => id y < id x) xs
    in
        qsort left @ [x] @ qsort right
    end

    (*--------------------------------------------------------------------*)
    (*--------------------------------------------------------------------*)


    (* Operations to manipulate SDD. Used by the cache. *)
    structure SDDOperations (* : OPERATION *) =
    struct

      val name = "SDD"

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

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
         Thus, it make usable by flatSquareUnion.

         (values ref * SDD) Vector.vector
           -> ( values ref * SDD list ) list

      *)
      fun alphaToList( alpha ) =
      Vector.foldr
        (fn (x,acc) => let val (vl,succ) = x in (vl,[succ])::acc end )
        []
        alpha

      (* Apply alphaToList to a node

         SDD
           -> ( values ref * SDD list ) list

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
        | _       => lookup(Union( qsort xs', lookup ))
      end

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

      (* Warning: duplicate code with SDD.intersection! Keep in sync! *)
      fun intersectionCallback lookup xs =
        case xs of
          []      => zero (* No need to cache *)
        | (x::[]) => x    (* No need to cache *)
        | _       => lookup(Inter( qsort xs, lookup))

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

       (* Merge all values that lead to the same successor,
          using an hash table.
          Returns an alpha suitable to build a new flat node with
          flatNodeAlpha.

          alpha : ( values ref * SDD list ) list
            -> ( values ref * SDD ) Vector.vector

          Warning! Duplicate logic with squareUnion!
       *)
       fun flatSquareUnion cacheLookup alpha =
       let
         (* This table associates a list of values sets to a single
            SDD successor *)
         val tbl :
           ( ( SDD , values ref list ref) HT.hash_table )
           = (HT.mkTable( fn x => hash(!x) , op = )
             ( 10000, DoNotPanic ))

         (* Fill the hash table *)
         val _ = app (fn ( vl, succs ) =>
                     let
                       val u = unionCallback cacheLookup succs
                     in
                       if Values.empty(!vl) then
                        ()
                       else
                         case HT.find tbl u of
                           NONE   => HT.insert tbl ( u, ref [vl] )
                           (* update list of values set *)
                         | SOME x => x := vl::(!x)
                     end
                     )
                     alpha

       val alpha' =
         HT.foldi (fn ( succ, vls, acc) =>
                          let
                            val vl = (case !vls of
                                       []      => raise DoNotPanic
                                     | (x::[]) => x
                                     | (x::xs) =>
                                         foldl (fn (y,acc) => valUnion[y,acc])
                                                x
                                                xs
                                     )
                         in
                           (vl,succ)::acc
                         end
                         )
                         []
                         tbl

        fun qsort [] = []
        |   qsort ((arcx as (x,_))::xs) =
        let
          val (left,right) = List.partition (fn (y,_) => Values.lt(!y,!x)) xs
        in
          qsort left @ [arcx] @ qsort right
        end

       in
         Vector.fromList (qsort alpha')
       end

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

       (* Merge all valuations that lead to the same successor,
          using an hash table.
          Returns an alpha suitable to build a new node with nodeAlpha.

          alpha : ( SDD * SDD list ) list
            -> ( SDD * SDD ) Vector.vector

          Warning! Duplicate logic with flatSquareUnion!
       *)
       fun squareUnion cacheLookup alpha =
       let
         (* This table associates a list of valuations to a single
            SDD successor *)
         val tbl :
           ( ( SDD , SDD list ref) HT.hash_table )
           = (HT.mkTable( fn x => hash(!x) , op = )
             ( 10000, DoNotPanic ))

         (* Fill the hash table *)
         val _ = app (fn ( vl, succs ) =>
                     let
                       val u = unionCallback cacheLookup succs
                     in
                       if vl = zero then
                        ()
                       else
                         case HT.find tbl u of
                           NONE   => HT.insert tbl ( u, ref [vl] )
                           (* update list of valuations *)
                         | SOME x => x := vl::(!x)
                     end
                     )
                     alpha
       in
         HT.foldi (fn ( succ, vls, acc) =>
                          let
                            val vl =
                              (case !vls of
                                []      => raise DoNotPanic
                              | (x::[]) => x
                              | (x::xs) =>
                                foldl (fn (y,acc) =>
                                       unionCallback cacheLookup [y,acc]
                                      )
                                      x
                                      xs
                              )
                         in
                           Vector.concat[acc,Vector.fromList[(vl,succ)]]
                         end
                         )
                         (Vector.fromList [])
                         tbl
       end

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
          val inter = valIntersection [aVal,bVal]
        in
          if Values.empty(!inter) then
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
         of type (values ref * SDD list ) list which stores all
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
                   (flatSquareUnion cacheLookup)
                   (flatCommonApply cacheLookup unionCallback)
                   valUnion
                   valDifference
                   (Values.empty o !)
                   flatNodeAlpha
                   xs var

        (* Hierarchical node case *)
        | HNode{variable=var,...} =>
          unionSDD alphaNodeToList
                   alphaToList
                   (squareUnion cacheLookup)
                   (commonApply cacheLookup unionCallback)
                   (unionCallback cacheLookup)
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
             (values ref,SDD list) list.
             This type is also used as the accumulator for the foldl
             on the list of operands, as it will be given to the
             square union operation.

             initial  : (values ref * SDD list) list
             operands : (values ref * SDD list) list list
          *)
          val ( initial, operands ) = case map flatAlphaNodeToList xs of
                                        []       => raise DoNotPanic
                                      | (y::ys)  => (y,ys)

          val flatCommonApply'
            = flatCommonApply cacheLookup intersectionCallback

          val flatSquareUnion' = flatSquareUnion cacheLookup

          (* Intersect two operands *)
          fun interHelper (xs,ys) = flatCommonApply'( xs, ys )

          val alpha = flatSquareUnion' ( foldl interHelper initial operands )

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

          val squareUnion' = squareUnion cacheLookup

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
          val bUnion = valUnion( map (fn (x,_)=>x) ralpha )
        in
          foldl (fn ((aVal,aSuccs),acc) =>
                  let
                    val diff = valDifference(aVal,bUnion)
                  in
                    if Values.empty(!diff) then
                      acc
                    else
                      ( diff, aSuccs)::acc
                  end
                )
                []
                lalpha
        end

        val flatSquareUnion' = flatSquareUnion cacheLookup
        val alpha = flatSquareUnion' ( diffPart @ commonPart )
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

        val squareUnion' = squareUnion cacheLookup
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
      case x of
        Union( xs, _ )    =>  (case y of
                                Union( ys, _ )  => xs = ys
                              | _               => false
                              )
      | Inter( xs, _ )    =>  (case y of
                                Inter( ys, _ ) => xs = ys
                              | _              => false
                              )
      | Diff( xl, xr, _ ) =>  (case y of
                                Diff( yl, yr, _ ) => xl = yl andalso xr = yr
                              | _ => false
                              )

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)


    end (* end struct SDDOperations *)

  in (* local SDD manipulations *)

    (* Cache of operations on SDDs *)
    structure SDDOpCache = CacheFun( structure Operation = SDDOperations )

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
      | _       => SDDOpCache.lookup(SDDOperations.Union( qsort xs'
                                                        , cacheLookup ))
    end

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)

    (* Warning! Duplicate code with SDD.SDDOperations.intersectionCallback! *)
    fun intersection xs =
    case xs of
      []      => zero (* No need to cache *)
    | (x::[]) => x    (* No need to cache *)
    | _       => SDDOpCache.lookup(SDDOperations.Inter( qsort xs
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

  fun alpha (x as (ref (iSDD(sdd,_,_)))) =
  let
    fun alphaHelper a f =
        Vector.foldr
        (fn (x,acc) => let val (vl,succ) = x in (f vl,succ)::acc end )
        []
        a
  in
    case sdd of
      Node{alpha=a,...}  => alphaHelper a (fn x => Values (!x))
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
  | Values(values) => Values.hash(values)

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  (* Compare two valuations. Needed by HomFun*)
  fun eqValuation (x,y) =
  case x of
    Nested(nestedx) => (case y of
                         Nested(nestedy) => nestedx = nestedy
                       | _               => false
                       )
  | Values(valuesx) => (case y of
                         Values(valuesy) => Values.eq( valuesx, valuesy )
                       | _               => false
                       )

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  (* Export a valuation to a string. Needed by HomFun*)
  fun valuationToString x =
  case x of
    Nested(nested) => toString nested
  | Values(values) => Values.toString values

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  (* Count the number of distinct paths in an SDD *)
  fun paths x =
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
                                        IntInf.fromInt(Values.length(!v))
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

  (* Export an SDD to a DOT representation *)
  fun toDot x =
  let

    fun terminal value =
      "terminal"
    ^ (Int.toString value)
    ^ " [shape=rectangle,regular=true,label=\""
    ^ (Int.toString value)
    ^ "\"]\n;"

    fun dotHelper (ref (iSDD(sdd,_,_))) =
    case sdd of
      Zero       => terminal 0
    | One        => terminal 1
    | Node{...}  => raise NotYetImplemented
    | HNode{...} => raise NotYetImplemented
  in
      "digraph sdd {\n"
    ^ (dotHelper x)
    ^ "\n}\n"
  end

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  fun stats () =
   (ValOpCache.stats()) ^ (SDDOpCache.stats())

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

end (* end functor SDDFun *)

(*--------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------*)

structure SDD = SDDFun( structure Variable  = IntVariable
                      ; structure Values    = DiscreteIntValues )

(*--------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------*)
