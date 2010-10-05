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
    in
      case sdd of
        Zero  => "|0|"
      | One   => "|1|"
      | Node{ variable=vr, alpha=alpha} =>
        (Variable.toString vr)
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
          val SDD(_,hash_next)    = !next
          val hash_values         = Valuation.hash values
          val h = Word32.xorb( Variable.hash var
                             , Word32.xorb( hash_next, hash_values ))
          val unik_values = ValUT.unify values
          val alpha = Vector.fromList [( unik_values, next )]
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
    val hash_alpha = Vector.foldl (fn ((vl,succ),h) =>
                                    Word32.xorb( Valuation.hash(!vl)
                                               , Word32.xorb( hash(!succ), h )
                                               )
                                  )
                     (Word32.fromInt 0)
                     alpha

    val h = Word32.xorb( Variable.hash var, hash_alpha )
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
  = raise NotYetImplemented

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
             this hash alongside the valuation? *)
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

      (* Transform the alpha of a node into :
         (valuation ref,SDD ref list) list *)
      fun flatAlphaToList( alpha : (valuation ref * SDD ref) Vector.vector )
        : ( valuation ref * SDD ref list ) list
      = Vector.foldr (fn (x,acc) => let
                                      val (vl,succ) = x
                                    in
                                      (vl,[succ])::acc
                                    end
                     )
                     []
                     alpha

      (* Transform the alpha of a node into :
         (valuation ref,SDD ref list) list *)
      fun flatAlphaNodeToList ( n : SDD ref )
        : ( valuation ref * SDD ref list ) list
      =
      let
        val alpha = case !n of
                      SDD(Node{alpha=alpha,...},_) => alpha
                    | _ => raise DoNotPanic
      in
        flatAlphaToList alpha
      end

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
        | _       => lookup(Union( qsort xs, lookup ))
      end

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

      (* Warning: duplicate code with SDD.intersection! Keep in sync! *)
      fun intersectionCallback ( lookup, xs ) =
        case xs of
          []      => zero (* No need to cache *)
        | (x::[]) => x    (* No need to cache *)
        | _       => lookup(Inter( qsort xs, lookup))

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

      (* Warning: duplicate code with SDD.intersection! Keep in sync! *)
      fun differenceCallback( lookup, x, y ) =
        if x = y then
          zero (* No need to cache *)
        else
          lookup(Diff( x, y, lookup ))

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

       (* Merge all valuations that lead to the same successor,
          using an hash table. *)
       fun flatSquareUnion lookup alpha =
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
                       val u = unionCallback( lookup, succs )
                     in
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

      fun flatCommonApply _ _         ( [], _ )    = []
      |   flatCommonApply lookup cont ( x::xs, ys) =
      let

        fun propagate _    ( _, [] )                       =  []
        |   propagate cont ( (a,a_succs), (b,b_succs)::_ ) =
        let
          val inter = valIntersection [a,b]
        in
          if Valuation.empty (!inter) then
            []
          else
            let
              val succ = cont( lookup, a_succs@b_succs )
            in
              if succ = zero then
                []
              else
                [ ( inter, [succ] ) ]
            end
        end

        val propagate'       = propagate cont
        val flatCommonApply' = flatCommonApply lookup cont
      in
        propagate' ( x, ys  ) @ flatCommonApply' (xs, ys )
      end

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

      (* Do the union of a list of SDDs. *)
      fun union( xs, lookup ) =
      let

        (* Check operands compatibility *)
        val _ = check xs

      in

        case !(hd xs) of

          (* All operands are |1| *)
          SDD(One,_)        => one

          (* There shouldn't be any |0| *)
        | SDD(Zero,_)       => raise DoNotPanic

          (* Flat node case *)
        | SDD(Node{...},_)  =>
        let

          (* The variable of the current level *)
          val var = case !(hd xs) of
                      SDD(Node{variable=v,...},_) => v
                    | _ => raise DoNotPanic

          val ( initial  : (valuation ref * SDD ref list) list
              , operands : (valuation ref * SDD ref list) list list
              )
          = case map flatAlphaNodeToList xs of
              []       => raise DoNotPanic
            |  (y::ys)  => (y,ys)

          (* Merge two operands *)
          fun unionHelper ( [], ( res, []) )
          = ( [], res )

          (* No more elements in alpha_a *)
          |   unionHelper ( [], ( res, bxs ))
          = ( [], bxs @ res )

          (* Empty intersection for a *)
          |   unionHelper ( (a,a_succs)::axs, ( res, [] ))
          = unionHelper ( axs, ( [], (a,a_succs)::res ) )

          (* General case *)
          |   unionHelper ( alpha_a as ((a,a_succs)::axs)
                      , ( res, (b,b_succs)::bxs )
                      )
          =
          if a = b then
            unionHelper ( axs
                    , ( ( a, a_succs@b_succs )::res
                      , bxs
                      )
                    )
          else
          let
            val inter = valIntersection [a,b]
          in
            if Valuation.empty(!inter) then
              unionHelper ( alpha_a
                          , ( ( b, b_succs )::res
                            , bxs
                            )
                          )
            else
            let
              val diff  = valDifference( a, inter )
            in
              if b = inter then (* No need to go further *)
                unionHelper ( ( diff, a_succs )::axs
                            , ( ( inter, a_succs@b_succs )::res
                              , bxs
                              )
                            )
                else
                let
                  val diff2 = valDifference( b, inter )
                in
                  unionHelper ( (diff, a_succs )::axs
                              , ( ( inter, a_succs@b_succs)::res
                                , ( diff2, b_succs)::bxs
                                )
                              )
                end
            end
          end

          val (_,tmp) = foldl unionHelper ([],initial) operands

          val flatSquareUnion' = flatSquareUnion lookup
          val alpha = flatSquareUnion' tmp

        in
          flatNodeAlpha( var, alpha )
        end

          (* Hierachical node case *)
        | SDD(HNode{...},_) => raise NotYetImplemented

      end (* end fun union *)

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

      fun intersection( xs, lookup ) =
      let

        (* Test if there are any zero in operands *)
        val has_zero = case List.find (fn x => case !x of
                                                 SDD(Zero,_) => true
                                               | _           => false
                                      )
                                      xs
                       of
                          NONE    => false
                        | SOME _  => true
      in

        (* Intersection of anything with |0| is always |0| *)
        if has_zero then
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

          val ( initial  : (valuation ref * SDD ref list) list
              , operands : (valuation ref * SDD ref list) list list )
          = case map flatAlphaNodeToList xs of
              []       => raise DoNotPanic
            |  (y::ys)  => (y,ys)


          val flatCommonApply' = flatCommonApply lookup intersectionCallback
          val flatSquareUnion' = flatSquareUnion lookup
          
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

      fun difference( (l,r), lookup ) =

        case !l of

          SDD(Zero,_) => (case !r of
                            SDD(Zero,_) => zero
                          | SDD(One,_)  => one
                          | _           => raise IncompatibleSDD
                          )

        | SDD(One,_)  => (case !r of
                            SDD(Zero,_) => one
                          | SDD(One,_)  => zero
                          | _           => raise IncompatibleSDD
                          )

        | SDD( Node{variable=lvr,alpha=la}, _ ) =>

        (case !r of
          SDD(Zero,_)       => raise IncompatibleSDD
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
                (x::y::[]) => differenceCallback( lookup, x, y )
              | _          => raise DoNotPanic

            val flatCommonApply' = flatCommonApply lookup callback
          in
            flatCommonApply'( lalpha, ralpha )
          end

          val diffPart =
          let
            val bUnion = valUnion( map (fn (x,_)=>x) ralpha )
          in
            foldl (fn ((a,a_succs),acc) =>
                    ( valDifference(a,bUnion), a_succs ) :: acc
                  )
                  []
                  lalpha
          end

          val flatSquareUnion' = flatSquareUnion lookup
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
          Union(xs,lookup)  => union( xs, lookup )
        | Inter(xs,lookup)  => intersection( xs, lookup )
        | Diff(x,y,lookup)  => difference( (x,y), lookup)

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

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
        | _       => SDDOpCache.lookup(SDDOperations.Union( qsort xs
                                                          , cacheLookup ))
      end

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)

    (* Warning! Duplicate code with SDD.SDDOperations.intersection! *)
    fun intersection xs =
      case xs of
        []      => zero (* No need to cache *)
      | (x::[]) => x    (* No need to cache *)
      | _       => SDDOpCache.lookup(SDDOperations.Inter( qsort xs
                                                        , cacheLookup ))

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)

    (* Warning! Duplicate code with SDD.SDDOperations.difference! *)
    fun difference(x,y) =
      if x = y then
        zero (* No need to cache *)
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
  fun toDot _         = raise NotYetImplemented

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

end (* end functor SDDFun *)

(*--------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------*)

structure SDD = SDDFun( structure Variable  = IntVariable
                      ; structure Valuation = DiscreteIntValuation )

(*--------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------*)
