(*--------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------*)

signature SDD =
sig

  type SDD
  type variable
  type valuation

  val zero          : SDD ref
  val one           : SDD ref
  val flatNode      : variable * valuation * SDD ref -> SDD ref
  val node          : variable * SDD ref * SDD ref -> SDD ref

  val union         : SDD ref list -> SDD ref
  val intersection  : SDD ref list -> SDD ref
  val difference    : SDD ref * SDD ref -> SDD ref

  val paths         : SDD ref -> int

  val toString      : SDD ref -> string
  val toDot         : SDD ref -> string

  exception IncompatibleSDD
  exception NotYetImplemented

end

(*--------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------*)

functor SDDFun ( structure Variable  : VARIABLE
               ; structure Valuation : VALUATION )
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
                             , alpha : (Valuation.t ref * t ref) Vector.vector
                             }
                  | HNode of { variable : Variable.t
                             , alpha : ( t ref * t ref ) Vector.vector
                             }

    (* Compare two SDDs *)
    fun eq (l,r) =
    let
      val SDD(lsdd,lh) = l
      val SDD(rsdd,rh) = r
    in
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

    end (* fun eq *)

    (* The hash value of a node is stored with it, because we can't
       use the address of the reference (like in C). Thus, it has to
       be computed by functions who construct SDD nodes. *)
    fun hash (SDD(_,h)) = h

  end (* end struct Definition *)
  open Definition

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  type SDD        = Definition.t
  type variable   = Variable.t
  type valuation  = Valuation.t

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  (* Unicity *)
  structure ValUT = UnicityTableFun( structure Data = Valuation )
  structure SDDUT = UnicityTableFun( structure Data = Definition )

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  exception IncompatibleSDD
  exception NotYetImplemented
  exception DoNotPanic

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
                                          Valuation.toString(!values)
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
  val zero : SDD ref
    = SDDUT.unify( SDD( Zero , MLton.hash 0 ) )

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  (* Return the |1| ("one") terminal *)
  val one : SDD ref
    = SDDUT.unify( SDD( One  , MLton.hash 1 ) )

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  (* Return a node with a set of discrete values on arc *)
  fun flatNode ( var : Variable.t , values : Valuation.t , next : SDD ref )
               : SDD ref

    = case !next of
      SDD(Zero,_) => zero
    | _           =>
      if Valuation.empty values then
        zero
      else
        let
          val SDD(_,hashNext)    = !next
          val hashValues         = Valuation.hash values
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
                    , alpha : (valuation ref * SDD ref ) Vector.vector )
  =
  if Vector.length alpha = 0 then
    zero
  else
  let
    val hashAlpha = Vector.foldl (fn ((vl,succ),h) =>
                                    Word32.xorb( Valuation.hash(!vl)
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

  (* Return a node with a nested node on arc *)
  fun node ( vr : Variable.t, nested : SDD ref , next : SDD ref )
           : SDD ref

    = case !next of
      SDD(Zero,_) => zero
    | _           =>
      case !nested of
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

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  (* Construct a node with an already computed alpha.
     For internal use only! *)
  fun nodeAlpha ( var   : Variable.t
                , alpha : (SDD ref * SDD ref ) Vector.vector )
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

  local (* Valuations manipulations *)

    (* Operations to manipulate valuations. Used by the cache. *)
    structure ValuationOperations (* : OPERATION *) =
    struct

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

      type result        = valuation ref
      datatype operation = Union of valuation ref list
                         | Inter of valuation ref list
                         | Diff  of valuation ref * valuation ref

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
          (* Valuation.hash(!x) -> problem: we have to compute again
             the hash value of the valuation... Maybe we should store
             this hash alongside of the valuation? *)
          fun hashOperands( h0, xs ) =
            foldl (fn(x,h) => Word32.xorb( Valuation.hash(!x), h)) h0 xs
        in
          case x of
            Union(xs) => hashOperands( Word32.fromInt 15411567, xs)
          | Inter(xs) => hashOperands( Word32.fromInt 78995947, xs)
          | Diff(l,r) => Word32.xorb( Word32.fromInt 94165961
                                    , Word32.xorb( Valuation.hash(!l)
                                                 , Valuation.hash(!r))
                                    )
        end

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

      (* Evaluation an operation on valuations. Called by CacheFun. *)
      fun apply operation =

        case operation of

          Union []     => raise DoNotPanic
        | Union(x::xs) =>
            ValUT.unify(foldl ( fn (x,res) => Valuation.union(!x,res) )
                              (!x)
                              xs
                        )

        | Inter []     => raise DoNotPanic
        | Inter(x::xs) =>
            ValUT.unify(foldl ( fn (x,res) => Valuation.intersection(!x,res) )
                              (!x)
                              xs
                        )

        | Diff(x,y)    => ValUT.unify( Valuation.difference( !x, !y) )

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

    end (* end structure ValuationOperations *)

    (*----------------------------------------------------------------------*)
    (*----------------------------------------------------------------------*)

    (* Cache of operations on valuations *)
    structure ValOpCache = CacheFun(structure Operation = ValuationOperations)

  in (* local valuations manipulations *)

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)

    fun valUnion xs =
      case xs of
        []      => raise DoNotPanic
      | (x::[]) => x (* No need to cache *)
      | _       => ValOpCache.lookup( ValuationOperations.Union(xs) )

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)

    fun valIntersection xs =
      case xs of
        []      => raise DoNotPanic
      | (x::[]) => x (* No need to cache *)
      | _       => ValOpCache.lookup( ValuationOperations.Inter(xs) )

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)

    fun valDifference(x,y) =
      let
        val empty = ValUT.unify( Valuation.mkEmpty() )
      in
        if x = y then
          empty
        else
          ValOpCache.lookup( ValuationOperations.Diff(x,y) )
      end

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)

  end (* local valuations manipulations *)

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

      type result        = SDD ref
      datatype operation = Union of
                              ( SDD ref list * (operation -> result) )
                         | Inter of
                              ( SDD ref list * (operation -> result) )
                         | Diff  of
                              ( SDD ref * SDD ref * (operation -> result) )

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
         (a list of valuations, each one leading to a list of successors).
         Thus, it make usable by flatSquareUnion.

         (valuation ref * SDD ref) Vector.vector
           -> ( valuation ref * SDD ref list ) list

         Warning! Duplicate logic with alphaToList!
      *)
      fun flatAlphaToList( alpha ) =
      Vector.foldr
        (fn (x,acc) => let val (vl,succ) = x in (vl,[succ])::acc end )
        []
        alpha

      (* Apply flatAlphaToList to a node

         SDD ref
           -> ( valuation ref * SDD ref list ) list

         Warning! Duplicate logic with alphaNodeToList!
      *)
      fun flatAlphaNodeToList n =
      case !n of
        SDD(Node{alpha=alpha,...},_) => flatAlphaToList alpha
      | _ => raise DoNotPanic

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

      (* Convert an alpha (a vector) into a more easy to manipulate type
         (a list of valuations, each one leading to a list of successors).
         Thus, it make usable by squareUnion.

         (SDD ref * SDD ref) Vector.vector
           -> ( SDD ref * SDD ref list ) list

         Warning! Duplicate logic with flatAlphaToList!
      *)
      fun alphaToList( alpha ) =
      Vector.foldr
        (fn (x,acc) => let val (vl,succ) = x in (vl,[succ])::acc end )
        []
        alpha

      (* Apply alphaToList to a node

         SDD ref
           -> ( SDD ref * SDD ref list ) list

         Warning! Duplicate logic with flatAlphaNodeToList!
      *)
      fun alphaNodeToList n =
      case !n of
        SDD(HNode{alpha=alpha,...},_) => alphaToList alpha
      | _ => raise DoNotPanic

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

      (* Warning: duplicate code with SDD.union! Keep in sync! *)
      fun unionCallback ( lookup, xs ) =
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
        | _       => lookup(Union( (*qsort*) xs, lookup ))
      end

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

      (* Warning: duplicate code with SDD.intersection! Keep in sync! *)
      fun intersectionCallback ( lookup, xs ) =
        case xs of
          []      => zero (* No need to cache *)
        | (x::[]) => x    (* No need to cache *)
        | _       => lookup(Inter( (*qsort*) xs, lookup))

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

      (* Warning: duplicate code with SDD.intersection! Keep in sync! *)
      fun differenceCallback( lookup, x, y ) =
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

       (* Merge all valuations that lead to the same successor,
          using an hash table.
          Returns an alpha suitable to build a new flat node with
          flatNodeAlpha.

          alpha : ( valuation ref * SDD ref list ) list
            -> ( valuation ref * SDD ref ) Vector.vector

          Warning! Duplicate logic with squareUnion!
       *)
       fun flatSquareUnion cacheLookup alpha =
       let
         (* This table associates a list of valuations to a single
            SDD successor *)
         val tbl :
           ( ( SDD ref , valuation ref list ref) HashTable.hash_table )
           = (HashTable.mkTable( fn x => hash(!x) , op = )
             ( 10000, DoNotPanic ))

         (* Fill the hash table *)
         val _ = app (fn ( vl, succs ) =>
                     let
                       val u = unionCallback( cacheLookup, succs )
                     in
                       if Valuation.empty(!vl) then
                        ()
                       else
                         case HashTable.find tbl u of
                           NONE   => HashTable.insert tbl ( u, ref [vl] )
                           (* update list of valuations *)
                         | SOME x => x := vl::(!x)
                     end
                     )
                     alpha
       in
         HashTable.foldi (fn ( succ, vls, acc) =>
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
                           Vector.concat[acc,Vector.fromList[(vl,succ)]]
                         end
                         )
                         (Vector.fromList [])
                         tbl
       end

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

       (* Merge all valuations that lead to the same successor,
          using an hash table.
          Returns an alpha suitable to build a new node with nodeAlpha.

          alpha : ( SDD ref * SDD ref list ) list
            -> ( SDD ref * SDD ref ) Vector.vector

          Warning! Duplicate logic with flatSquareUnion!
       *)
       fun squareUnion cacheLookup alpha =
       let
         (* This table associates a list of valuations to a single
            SDD successor *)
         val tbl :
           ( ( SDD ref , SDD ref list ref) HashTable.hash_table )
           = (HashTable.mkTable( fn x => hash(!x) , op = )
             ( 10000, DoNotPanic ))

         (* Fill the hash table *)
         val _ = app (fn ( vl, succs ) =>
                     let
                       val u = unionCallback( cacheLookup, succs )
                     in
                       if vl = zero then
                        ()
                       else
                         case HashTable.find tbl u of
                           NONE   => HashTable.insert tbl ( u, ref [vl] )
                           (* update list of valuations *)
                         | SOME x => x := vl::(!x)
                     end
                     )
                     alpha
       in
         HashTable.foldi (fn ( succ, vls, acc) =>
                          let
                            val vl =
                              (case !vls of
                                []      => raise DoNotPanic
                              | (x::[]) => x
                              | (x::xs) =>
                                foldl (fn (y,acc) =>
                                       unionCallback( cacheLookup,[y,acc])
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
          if Valuation.empty(!inter) then
            propagate ( aArc, bAlpha)
          else
            let
              val succ = cont( lookup, aSuccs@bSuccs )
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
          val inter = intersectionCallback (lookup, [aVal,bVal])
        in
          if inter = zero then
            propagate ( aArc, bAlpha)
          else
            let
              val succ = cont( lookup, aSuccs@bSuccs )
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
         of type (valuation ref * SDD ref list ) list which stores all
         successors for a given valuation, which is then given to
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
        | SDD(Node{...},_)  =>
        let

          (* The variable of the current level *)
          val var = case !(hd xs) of SDD(Node{variable=v,...},_) => v
                                   | _ => raise DoNotPanic

          (* Transform the alpha of each node into :
             (valuation ref,SDD ref list) list.
             This type is also used as the accumulator for the foldl
             on the list of operands, as it will be given to the
             square union operation.

             initial  : (valuation ref * SDD ref list) list
             operands : (valuation ref * SDD ref list) list list
          *)
          val ( initial, operands ) = case map flatAlphaNodeToList xs of
                                        []       => raise DoNotPanic
                                      | (y::ys)  => (y,ys)

          (* Perform the union of the alpha of two operands *)
          (* Both aAlpha and bAlpha are empty, everything is in res *)
          fun unionHelper ( [], ( res, []) )
          = ( [], res )

          (* No more elements in aAlpha *)
          |   unionHelper ( [], ( res, bAlpha ))
          = ( [], bAlpha @ res )

          (* Empty intersection for a *)
          |   unionHelper ( (aVal,aSuccs)::aAlpha, ( res, [] ))
          = unionHelper ( aAlpha, ( [], (aVal,aSuccs)::res ) )

          (* General case *)
          |   unionHelper ( aWholeAlpha as ((aVal,aSuccs)::aAlpha)
                          , ( res, (bArc as (bVal,bSuccs))::bAlpha ) )
          =
          (* Same valuation, we just need to merge the lists of successors. *)
          if aVal = bVal then
            unionHelper ( aAlpha
                        , ( ( aVal, aSuccs@bSuccs )::res
                          , bAlpha
                          )
                        )
          else
          let
            val inter = valIntersection [aVal,bVal]
          in
            (* Is there any common part between the two current valuations?
               If not, we just need to store the current b -> b_succs into res
               as a potential element of the future alpha, and move on to the
               next valuation of b's alpha.
            *)
            if Valuation.empty(!inter) then
              unionHelper ( aWholeAlpha
                          , ( bArc::res
                            , bAlpha
                            )
                          )
            else
            let
              val diff  = valDifference( aVal, inter )
            in
              if bVal = inter then (* No need to go further *)
                unionHelper ( ( diff, aSuccs )::aAlpha
                            , ( ( inter, aSuccs@bSuccs )::res
                              , bAlpha
                              )
                            )
              else
              let
                val diff2 = valDifference( bVal, inter )
              in
                unionHelper ( (diff, aSuccs )::aAlpha
                            , ( ( inter, aSuccs@bSuccs)::res
                              , ( diff2, bSuccs)::bAlpha
                              )
                            )
              end
            end
          end

          val (_,tmp) = foldl unionHelper ([],initial) operands

          val flatSquareUnion' = flatSquareUnion cacheLookup
          val alpha = flatSquareUnion' tmp

        in
          flatNodeAlpha( var, alpha )
        end (* Flat node case *)

        (* Hierachical node case
           Warning! Duplicate logic with the SDD(Node{...},_) case above!
        *)
        | SDD(HNode{...},_) =>
        let

          (* The variable of the current level *)
          val var = case !(hd xs) of SDD(HNode{variable=v,...},_) => v
                                   | _ => raise DoNotPanic

          (* Transform the alpha of each node into :
             (SDD ref,SDD ref list) list.
             This type is also used as the accumulator for the foldl
             on the list of operands, as it will be given to the
             square union operation.

             initial  : (SDD ref * SDD ref list) list
             operands : (SDD ref * SDD ref list) list list
          *)
          val ( initial, operands ) = case map alphaNodeToList xs of
                                        []       => raise DoNotPanic
                                      | (y::ys)  => (y,ys)

          (* Perform the union of the alpha of two operands *)
          (* Both aAlpha and bAlpha are empty, everything is in res *)
          fun unionHelper ( [], ( res, []) )
          = ( [], res )

          (* No more elements in aAlpha *)
          |   unionHelper ( [], ( res, bAlpha ))
          = ( [], bAlpha @ res )

          (* Empty intersection for a *)
          |   unionHelper ( (aVal,aSuccs)::aAlpha, ( res, [] ))
          = unionHelper ( aAlpha, ( [], (aVal,aSuccs)::res ) )

          (* General case *)
          |   unionHelper ( aWholeAlpha as ((aVal,aSuccs)::aAlpha)
                          , ( res, (bArc as (bVal,bSuccs))::bAlpha ) )
          =
          (* Same valuation, we just need to merge the lists of successors. *)
          if aVal = bVal then
            unionHelper ( aAlpha
                        , ( ( aVal, aSuccs@bSuccs )::res
                          , bAlpha
                          )
                        )
          else
          let
            val inter = intersectionCallback( cacheLookup, [aVal,bVal] )
          in
            (* Is there any common part between the two current valuations?
               If not, we just need to store the current b -> b_succs into res
               as a potential element of the future alpha, and move on to the
               next valuation of b's alpha.
            *)
            if inter = zero then
              unionHelper ( aWholeAlpha
                          , ( bArc::res
                            , bAlpha
                            )
                          )
            else
            let
              val diff  = differenceCallback( cacheLookup, aVal, inter )
            in
              if bVal = inter then (* No need to go further *)
                unionHelper ( ( diff, aSuccs )::aAlpha
                            , ( ( inter, aSuccs@bSuccs )::res
                              , bAlpha
                              )
                            )
              else
              let
                val diff2 = differenceCallback( cacheLookup, bVal, inter )
              in
                unionHelper ( (diff, aSuccs )::aAlpha
                            , ( ( inter, aSuccs@bSuccs)::res
                              , ( diff2, bSuccs)::bAlpha
                              )
                            )
              end
            end
          end

          val (_,tmp) = foldl unionHelper ([],initial) operands

          val squareUnion' = squareUnion cacheLookup
          val alpha = squareUnion' tmp

        in
          nodeAlpha( var, alpha )
        end (* Hierarchical node case *)

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
             (valuation ref,SDD ref list) list.
             This type is also used as the accumulator for the foldl
             on the list of operands, as it will be given to the
             square union operation.

             initial  : (valuation ref * SDD ref list) list
             operands : (valuation ref * SDD ref list) list list
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
        end

        (* Hierachical node case *)
        | SDD(HNode{...},_)  => raise NotYetImplemented

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

        val lalpha = flatAlphaToList la
        val ralpha = flatAlphaToList ra

        val commonPart =
        let
          (* Difference is a binary operation, while flatCommonApply
             expects an n-ary operation *)
          fun callback( lookup, xs ) =
            case xs of
              (x::y::[]) => differenceCallback( cacheLookup, x, y )
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
                    if Valuation.empty(!diff) then
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
      | SDD( HNode{variable=lvr,alpha=lalpha}, _ ) =>
          raise NotYetImplemented

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

    (* Warning! Duplicate code with SDD.SDDOperations.union! *)
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
      | _       => SDDOpCache.lookup(SDDOperations.Union( (*qsort*) xs
                                                        , cacheLookup ))
    end

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)

    (* Warning! Duplicate code with SDD.SDDOperations.intersection! *)
    fun intersection xs =
    case xs of
      []      => zero (* No need to cache *)
    | (x::[]) => x    (* No need to cache *)
    | _       => SDDOpCache.lookup(SDDOperations.Inter( (*qsort*) xs
                                                        , cacheLookup ))

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)

    (* Warning! Duplicate code with SDD.SDDOperations.difference! *)
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

  (* Count the number of distinct paths in an SDD *)
  fun paths x =
    let
      val cache : (( SDD ref , int ) HashTable.hash_table) ref
          = ref (HashTable.mkTable( fn x => hash(!x) , op = )
                                  ( 10000, DoNotPanic ))
      fun pathsHelper x =
        let
          val SDD(sdd,_) = !x
        in
            case sdd of
            Zero  =>  0
          | One   =>  1
          | Node{alpha=(arcs),...} =>
              (case (HashTable.find (!cache) x) of
                SOME r => r
              | NONE   =>
                let
                  val value = Vector.foldl
                                    ( fn ((v,succ), n ) =>
                                      ( n + Valuation.length(!v) )
                                      * (pathsHelper succ )
                                    )
                                    0
                                    arcs
                  val _     = HashTable.insert (!cache) ( x, value )
                in
                  value
                end
              )

          | HNode{alpha=(arcs),...} =>
              (case (HashTable.find (!cache) x) of
                SOME r => r
              | NONE   =>
                let
                  val value = Vector.foldl
                                    ( fn ((v,succ), n ) =>
                                      ( n + pathsHelper v )
                                      * ( pathsHelper succ )
                                    )
                                    0
                                    arcs
                  val _     = HashTable.insert (!cache) ( x, value )
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
  fun toDot x         =
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
                      ; structure Valuation = DiscreteIntValuation )

(*--------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------*)
