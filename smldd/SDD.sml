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
  val hash              : SDD -> Word32.word
  val hashValuation     : valuation -> Word32.word
  val eqValuation       : (valuation * valuation) -> bool
  val valuationToString : valuation -> string

  val paths             : SDD -> int

  val toString          : SDD -> string
  val toDot             : SDD -> string

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

    datatype t    = SDD of ( sdd * Word32.word ) (* Word32.word: hash value *)
    and sdd       = Zero
                  | One
                  | Node of  { variable : Variable.t
                             , alpha : (Values.t ref * t ref) Vector.vector
                             }
                  | HNode of { variable : Variable.t
                             , alpha : ( t ref * t ref ) Vector.vector
                             }

    (* Compare two SDDs *)
    fun eq ( SDD(lsdd,lh), SDD(rsdd,rh) ) =
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
    fun hash (SDD(_,h)) = h

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
  structure ValUT = UnicityTableFun( structure Data = Values )
  structure SDDUT = UnicityTableFun( structure Data = Definition )

  structure H = HashTable

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  exception IncompatibleSDD
  exception NotYetImplemented
  exception DoNotPanic
  exception IsNotANode

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  (* Export an SDD to a string *)
  fun toString x =
    let
      val SDD(sdd,_) = !x
      (*val SDD(_,h) = !x*)
    in
      case sdd of
        Zero  => "|0|"
      | One   => "|1|"
      | Node{ variable=vr, alpha=alpha} =>
          "(" ^ (Variable.toString vr) ^ ")"
        (*^ " #" ^ (Word32.toString h) ^ "#"*)
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
    end (* end fun toString *)

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  (* Return the |0| ("zero") terminal *)
  val zero = SDDUT.unify( SDD( Zero , MLton.hash 0 ) )

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  (* Return the |1| ("one") terminal *)
  val one = SDDUT.unify( SDD( One  , MLton.hash 1 ) )

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  (* Return a node with a set of discrete values on arc *)
  fun flatNode ( var : Variable.t , values : Values.t , next : SDD )
    = case !next of
      SDD(Zero,_) => zero
    | _           =>
      if Values.empty values then
        zero
      else
        let
          val SDD(_,hashNext)    = !next
          val hashValues         = Values.hash values
          val h = Word32.xorb( Variable.hash var
                             , Word32.xorb( hashNext, hashValues ))
          val unikValues = ValUT.unify values
          val alpha = Vector.fromList [( unikValues, next )]
        in
          SDDUT.unify( SDD( Node{ variable=var, alpha=alpha}, h) )
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
                                    Word32.xorb( Values.hash(!vl)
                                               , Word32.xorb( hash(!succ), h )
                                               )
                                  )
                     (Word32.fromInt 0)
                     alpha

    val h = Word32.xorb( Variable.hash var, hashAlpha )
  in
    SDDUT.unify( SDD( Node{variable=var,alpha=alpha}, h) )
  end

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  (* Return an hierarchical  node *)
  fun hierNode ( vr : Variable.t, nested : SDD , next : SDD ) =
  case !next of
    SDD(Zero,_) => zero
  | _           =>
  ( case !nested of
      SDD(Zero,_) => zero
    | _           =>
      let
        val SDD(_,hash_next)    = !next
        val SDD(_,hash_nested)  = !nested
        val h = Word32.xorb( Variable.hash vr
                           , Word32.xorb( hash_next, hash_nested ) )
        val alpha = Vector.fromList [( nested, next )]
      in
        SDDUT.unify( SDD(HNode{ variable=vr, alpha=alpha}, h) )
      end
  )

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  (* Construct a node with an already computed alpha.
     For internal use only! *)
  fun nodeAlpha ( var   : Variable.t , alpha : (SDD * SDD) Vector.vector )
  = if Vector.length alpha = 0 then
    zero
  else
  let
    val hashAlpha = Vector.foldl (fn ((vl,succ),h) =>
                                    Word32.xorb( hash (!vl)
                                               , Word32.xorb( hash(!succ), h )
                                               )
                                  )
                     (Word32.fromInt 0)
                     alpha

    val h = Word32.xorb( Variable.hash var, hashAlpha )
  in
    SDDUT.unify( SDD( HNode{variable=var,alpha=alpha}, h) )
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
            foldl (fn(x,h) => Word32.xorb( Values.hash(!x), h)) h0 xs
        in
          case x of
            Union(xs) => hashOperands( Word32.fromInt 15411567, xs)
          | Inter(xs) => hashOperands( Word32.fromInt 78995947, xs)
          | Diff(l,r) => Word32.xorb( Word32.fromInt 94165961
                                    , Word32.xorb( Values.hash(!l)
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

    (*----------------------------------------------------------------------*)
    (*----------------------------------------------------------------------*)

    (* Cache of operations on valuess *)
    structure ValOpCache = CacheFun(structure Operation = ValuesOperations)

  in (* local values manipulations *)

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

  end (* local valuess manipulations *)

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  local (* SDD manipulation *)

    (* Sort operands of union and intersection, using their hash values *)
    fun qsort []       = []
    |   qsort (x::xs)  =
    let
      fun hashOperand x = let val SDD(_,res) = !x in res end
    in
        qsort (List.filter (fn y => (hashOperand y) < (hashOperand x) )  xs )
      @ [x]
      @ qsort (List.filter (fn y => (hashOperand y) >= (hashOperand x) ) xs )
    end

    (*--------------------------------------------------------------------*)
    (*--------------------------------------------------------------------*)


    (* Operations to manipulate SDD. Used by the cache. *)
    structure SDDOperations (* : OPERATION *) =
    struct

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

        foldl (fn (x,y) =>

                case !x of

                    SDD(One,_)  =>
                      (case !y of
                        SDD(One,_) => y
                      | _ => raise IncompatibleSDD
                      )

                  | SDD(Node{variable=var1,...},_) =>
                      (case !y of
                        SDD(Node{variable=var2,...},_) =>
                          if not( Variable.eq( var1, var2 ) ) then
                            raise IncompatibleSDD
                          else
                            y
                      | _ => raise IncompatibleSDD
                      )

                  | SDD(HNode{variable=var1,...},_) =>
                      (case !y of
                        SDD(HNode{variable=var2,...},_) =>
                          if not( Variable.eq( var1, var2 ) ) then
                            raise IncompatibleSDD
                          else
                            y
                      | _ => raise IncompatibleSDD
                      )

                  (* Zero should have been filtered out *)
                  | SDD(Zero,_) => raise DoNotPanic
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
        SDD(Node{alpha=alpha,...},_) => alphaToList alpha
      | _ => raise DoNotPanic

      (* Apply alphaToList to a node

         SDD
           -> ( SDD * SDD list ) list

         Warning! Duplicate logic with flatAlphaNodeToList!
      *)
      fun alphaNodeToList n =
      case !n of
        SDD(HNode{alpha=alpha,...},_) => alphaToList alpha
      | _ => raise DoNotPanic

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

      (* Warning: duplicate code with SDD.union! Keep in sync! *)
      fun unionCallback lookup xs =
      let
        (* Remove all |0| *)
        val xs' = List.filter (fn x => case !x of
                                        SDD(Zero,_) => false
                                      | _           => true
                              )
                              xs
      in
        case xs' of
          []      => zero   (* No need to cache *)
        | (x::[]) => x      (* No need to cache *)
        | _       => lookup(Union( (*qsort*) xs', lookup ))
      end

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

      (* Warning: duplicate code with SDD.intersection! Keep in sync! *)
      fun intersectionCallback lookup xs =
        case xs of
          []      => zero (* No need to cache *)
        | (x::[]) => x    (* No need to cache *)
        | _       => lookup(Inter( (*qsort*) xs, lookup))

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
           ( ( SDD , values ref list ref) H.hash_table )
           = (H.mkTable( fn x => hash(!x) , op = )
             ( 10000, DoNotPanic ))

         (* Fill the hash table *)
         val _ = app (fn ( vl, succs ) =>
                     let
                       val u = unionCallback cacheLookup succs
                     in
                       if Values.empty(!vl) then
                        ()
                       else
                         case H.find tbl u of
                           NONE   => H.insert tbl ( u, ref [vl] )
                           (* update list of values set *)
                         | SOME x => x := vl::(!x)
                     end
                     )
                     alpha

       val alpha' =
         H.foldi (fn ( succ, vls, acc) =>
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
           ( ( SDD , SDD list ref) H.hash_table )
           = (H.mkTable( fn x => hash(!x) , op = )
             ( 10000, DoNotPanic ))

         (* Fill the hash table *)
         val _ = app (fn ( vl, succs ) =>
                     let
                       val u = unionCallback cacheLookup succs
                     in
                       if vl = zero then
                        ()
                       else
                         case H.find tbl u of
                           NONE   => H.insert tbl ( u, ref [vl] )
                           (* update list of valuations *)
                         | SOME x => x := vl::(!x)
                     end
                     )
                     alpha
       in
         H.foldi (fn ( succ, vls, acc) =>
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

        case !(hd xs) of

          (* All operands are |1| *)
          SDD(One,_)        => one

          (* There shouldn't be any |0|, they should have been filtered
             before querying the cache.
          *)
        | SDD(Zero,_)       => raise DoNotPanic

          (* Flat node case *)
        | SDD(Node{variable=var,...},_)  =>
        let
          val ( initial, operands ) = case map flatAlphaNodeToList xs of
                                        []       => raise DoNotPanic
                                      | (y::ys)  => (y,ys)


          val flatSquareUnion' = flatSquareUnion cacheLookup

          fun unionHelper ( lalpha, ralpha ) =
          let

            val commonPart =
              let
                val flatCommonApply' = flatCommonApply cacheLookup
                                                       unionCallback
              in
                flatCommonApply'( lalpha, ralpha )
              end

            val diffPartAB =
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

            val diffPartBA =
            let
              val aUnion = valUnion( map (fn (x,_)=>x) lalpha )
            in
              foldl (fn ((bVal,bSuccs),acc) =>
                      let
                        val diff = valDifference(bVal,aUnion)
                      in
                        if Values.empty(!diff) then
                          acc
                        else
                          ( diff, bSuccs)::acc
                      end
                    )
                    []
                    ralpha
            end

          in
            alphaToList
            (
              flatSquareUnion' (diffPartAB @ commonPart @ diffPartBA)
            )
          end

        in
          flatNodeAlpha( var
                       , flatSquareUnion'(foldl unionHelper initial operands)
                       )
        end (* Flat node case *)

        (* Hierachical node case
           Warning! Duplicate logic with the SDD(Node{...},_) case above!
        *)
        | SDD(HNode{...},_) => raise NotYetImplemented

      end (* end fun union *)

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

      (* N-ary intersection of SDDs *)
      fun intersection cacheLookup xs =
      let

        (* Test if there are any zero in operands *)
        val hasZero = case List.find (fn x => case !x of
                                                SDD(Zero,_) => true
                                              | _           => false
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
          case !(hd xs) of

        (* All operands are |1| *)
          SDD(One,_)        => check xs

        (* There shouldn't be any |0| *)
        | SDD(Zero,_)       => raise DoNotPanic

        (* Flat node case *)
        | SDD(Node{...},_)  =>
        let
          (* Check operands compatibility *)
          val _ = check xs

          (* The variable of the current level *)
          val var = case !(hd xs) of
                      SDD(Node{variable=v,...},_) => v
                    | _ => raise DoNotPanic

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
        | SDD(HNode{...},_)  =>
        let
          (* Check operands compatibility *)
          val _ = check xs

          (* The variable of the current level *)
          val var = case !(hd xs) of
                      SDD(HNode{variable=v,...},_) => v
                    | _ => raise DoNotPanic

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
      fun difference cacheLookup (l,r) =
      case !l of

        SDD(Zero,_) => raise DoNotPanic

      | SDD(One,_)  => (case !r of
                         SDD(Zero,_) => raise DoNotPanic
                       | SDD(One,_)  => zero
                       | _           => raise IncompatibleSDD
                       )

      | SDD( Node{variable=lvr,alpha=la}, _ ) =>

      (case !r of
        SDD(Zero,_)       => raise DoNotPanic
      | SDD(One,_)        => raise IncompatibleSDD
      | SDD(HNode{...},_) => raise IncompatibleSDD

      (* Difference of two flat nodes *)
      | SDD( Node{variable=rvr,alpha=ra}, _ ) =>
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
      | SDD( HNode{variable=lvr,alpha=la}, _ ) =>

      (case !r of
        SDD(Zero,_)       => raise DoNotPanic
      | SDD(One,_)        => raise IncompatibleSDD
      | SDD(Node{...},_)  => raise IncompatibleSDD

      (* Difference of two hiearchical nodes *)
      | SDD( HNode{variable=rvr,alpha=ra}, _ ) =>
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
          foldl (fn(x,h) => Word32.xorb( Definition.hash(!x), h)) h0 xs
      in
        case x of
          Union(xs,_)  => hashOperands( Word32.fromInt 15411567, xs)
        | Inter(xs,_ ) => hashOperands( Word32.fromInt 78995947, xs)
        | Diff(l,r,_)  => Word32.xorb( Word32.fromInt 94169137
                                     , Word32.xorb( Definition.hash(!l)
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

    (*--------------------------------------------------------------------*)
    (*--------------------------------------------------------------------*)

    (* Cache of operations on SDDs *)
    structure SDDOpCache = CacheFun( structure Operation = SDDOperations )

    (* Let operations in Op call the cache *)
    val cacheLookup = SDDOpCache.lookup

  in (* local SDD manipulations *)

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)

    (* Warning! Duplicate code with SDD.SDDOperations.unionCallback! *)
    fun union xs =
    let
      (* Remove all |0| *)
      val xs' = List.filter (fn x => case !x of
                                       SDD(Zero,_) => false
                                     | _           => true
                            )
                            xs
    in
      case xs' of
        []      => zero (* No need to cache *)
      | (x::[]) => x    (* No need to cache *)
      | _       => SDDOpCache.lookup(SDDOperations.Union( (*qsort*) xs'
                                                        , cacheLookup ))
    end

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)

    (* Warning! Duplicate code with SDD.SDDOperations.intersectionCallback! *)
    fun intersection xs =
    case xs of
      []      => zero (* No need to cache *)
    | (x::[]) => x    (* No need to cache *)
    | _       => SDDOpCache.lookup(SDDOperations.Inter( (*qsort*) xs
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
  fun variable x =
  case !x of
    SDD(Node{variable=var,...},_)  => var
  | SDD(HNode{variable=var,...},_) => var
  | _                              => raise IsNotANode

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  fun alpha x =
  let
    fun alphaHelper a f =
        Vector.foldr
        (fn (x,acc) => let val (vl,succ) = x in (f vl,succ)::acc end )
        []
        a
  in
    case !x of
      SDD(Node{alpha=a,...},_)  => alphaHelper a (fn x => Values (!x))
    | SDD(HNode{alpha=a,...},_) => alphaHelper a (fn x => Nested x)
    | _                         => raise IsNotANode
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
      val cache : (( SDD, int ) H.hash_table) ref
          = ref ( H.mkTable( fn x => hash x , op = )
                           ( 10000, DoNotPanic ) )
      fun pathsHelper x =
        let
          val SDD(sdd,_) = !x
        in
            case sdd of
            Zero  =>  0
          | One   =>  1
          | Node{alpha=(arcs),...} =>
              (case H.find (!cache) x of
                SOME r => r
              | NONE   =>
                let
                  val value = Vector.foldl
                                    ( fn ((v,succ), n ) =>
                                      n
                                      + ( ( Values.length(!v) )
                                          * (pathsHelper succ )
                                        )
                                    )
                                    0
                                    arcs
                  val _     = H.insert (!cache) ( x, value )
                in
                  value
                end
              )

          | HNode{alpha=(arcs),...} =>
              (case H.find (!cache) x of
                SOME r => r
              | NONE   =>
                let
                  val value = Vector.foldl
                                    ( fn ((v,succ), n ) =>
                                      n + ( pathsHelper v )
                                      * ( pathsHelper succ )
                                    )
                                    0
                                    arcs
                  val _     = H.insert (!cache) ( x, value )
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

    fun dotHelper x =
    case !x of
      SDD( Zero, _ ) => terminal 0
    | SDD( One, _ )  => terminal 1
    | SDD( Node{...}, _ )  => raise NotYetImplemented
    | SDD( HNode{...}, _ ) => raise NotYetImplemented
  in
      "digraph sdd {\n"
    ^ (dotHelper x)
    ^ "\n}\n"
  end

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

end (* end functor SDDFun *)

(*--------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------*)

structure SDD = SDDFun( structure Variable  = IntVariable
                      ; structure Values    = DiscreteIntValues )

(*--------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------*)
