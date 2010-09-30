(*--------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------*)

signature SDD =
sig

  type SDD
  type variable
  type valuation

  val zero          : SDD ref
  val one           : SDD ref
  val flat_node     : variable * valuation * SDD ref -> SDD ref
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
  fun flat_node ( vr : Variable.t , values : Valuation.t , next : SDD ref )
                : SDD ref

    = case !next of
      SDD(Zero,_) => zero
    | _           =>
      if Valuation.length values = 0 then
        zero
      else
        let
          val SDD(_,hash_next)    = !next
          val hash_values         = Valuation.hash values
          val h = Word32.xorb( Variable.hash vr
                             , Word32.xorb( hash_next, hash_values ))
          val unik_values = ValUT.unify values
          val alpha = Vector.fromList [( unik_values, next )]
        in
          SDDUT.unify( SDD( Node{ variable=vr, alpha=alpha}, h) )
        end

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  (* Return a node with a nested node on arc *)
  fun node  ( vr : Variable.t, nested : SDD ref , next : SDD ref )
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
          fun hash_operands( h0, xs ) =
            foldl (fn(x,h) => Word32.xorb( Valuation.hash(!x), h)) h0 xs
        in
          case x of
            Union(xs) => hash_operands( Word32.fromInt 15411567, xs)
          | Inter(xs) => hash_operands( Word32.fromInt 78995947, xs)
          | Diff(l,r) => Word32.xorb( Word32.fromInt 94165961
                                    , Word32.xorb( Valuation.hash(!l)
                                                 , Valuation.hash(!r))
                                    )
        end

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

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

    fun val_union xs =
      case xs of
        []      => raise DoNotPanic
      | (x::[]) => x (* No need to cache *)
      | _       => ValOpCache.lookup( ValuationOperations.Union(xs) )

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)

    fun val_intersection xs =
      case xs of
        []      => raise DoNotPanic
      | (x::[]) => x (* No need to cache *)
      | _       => ValOpCache.lookup( ValuationOperations.Inter(xs) )

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)

    fun val_difference(x,y) =
      ValOpCache.lookup( ValuationOperations.Diff(x,y) )

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)

  end (* local valuations manipulations *)

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  local (* SDD manipulation *)

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

      fun union( xs, lookup ) =
      let

        (* Remove |0| *)
        val xs' = List.filter (fn x => case !x of
                                          SDD(Zero,_) => false
                                        | _           => true
                              )
                              xs

        (* Check operands compatibility *)
        val _ = check xs'

      in

        case !(hd xs') of

          SDD(One,_)        => one
        | SDD(Zero,_)       => raise DoNotPanic

        | SDD(Node{...},_)  =>
        let
          (* Convert all operands into Node{...} *)
          val xs'' = map (fn x => case !x of
                                    SDD( n as Node{...}, _ ) => n
                                  | _ => raise DoNotPanic
                         )
                         xs'
        in
          raise NotYetImplemented
        end

        | SDD(HNode{...},_) =>
        let
          (* Convert all operands into HNode{...} *)
          val xs'' = map (fn x => case !x of
                                    SDD( n as HNode{...}, _ ) => n
                                  | _ => raise DoNotPanic
                         )
                         xs'
        in
          raise NotYetImplemented
        end

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
        (* Intersection with |0| is always |0| *)
        if has_zero then
          zero
        else
          (* Check operands compatibility *)
          check xs;
          raise NotYetImplemented
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

        | SDD( Node{variable=lvr,alpha=lalpha}, _ ) =>
            (case !r of
              SDD(Zero,_)       => raise IncompatibleSDD
            | SDD(One,_)        => raise IncompatibleSDD
            | SDD(HNode{...},_) => raise IncompatibleSDD
            | SDD(Node{variable=rvr,alpha=ralpha},_) => 
                if not( Variable.eq(lvr,rvr) ) then
                  raise IncompatibleSDD
                else
                  raise NotYetImplemented
            )

        | SDD( HNode{variable=lvr,alpha=lalpha}, _ ) =>
            raise NotYetImplemented

      (* end fun difference *)

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

      (* Apply an SDD operation. *)
      fun apply x =
        case x of
          Union(xs,lookup)  => union( xs, lookup )
        | Inter(xs,lookup)  => intersection( xs, lookup )
        | Diff(x,y,lookup)  => difference( (x,y), lookup)

      (*------------------------------------------------------------------*)
      (*------------------------------------------------------------------*)

      fun hash x =
        let
          fun hash_operands( h0, xs ) = 
            foldl (fn(x,h) => Word32.xorb( Definition.hash(!x), h)) h0 xs
        in        
          case x of
            Union(xs,_)  => hash_operands( Word32.fromInt 15411567, xs)
          | Inter(xs,_ ) => hash_operands( Word32.fromInt 78995947, xs)
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
    val lookup_cache    = SDDOpCache.lookup

    (* Sort operands of union and intersection, using their hash values *)
    fun qsort []       = []
    |   qsort (x::xs)  =
    let
      fun h x = let val SDD(_,res) = !x in res end
    in
        qsort (List.filter (fn y => (h y) < (h x) )  xs )
      @ [x]
      @ qsort (List.filter (fn y => (h y) >= (h x) ) xs )
    end

  in (* local SDD manipulations *)

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)

    fun union xs =
      case xs of
        []      => zero (* No need to cache *)
      | (x::[]) => x    (* No need to cache *)
      | _       => SDDOpCache.lookup(SDDOperations.Union( qsort xs
                                                        , lookup_cache ))

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)

    fun intersection xs =
      case xs of
        []      => zero (* No need to cache *)
      | (x::[]) => x    (* No need to cache *)
      | _       => SDDOpCache.lookup(SDDOperations.Inter( qsort xs
                                                        , lookup_cache ))

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)

    fun difference(x,y) =
      if x = y then
        zero (* No need to cache *)
      else
        SDDOpCache.lookup(SDDOperations.Diff( x, y, lookup_cache ))

    (*------------------------------------------------------------------*)
    (*------------------------------------------------------------------*)

  end (* local SDD manipulations *)

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  (* Count the number of distinct paths in a SDD *)
  fun paths x =
    let
      val cache : (( SDD ref , int ) HashTable.hash_table) ref
          = ref (HashTable.mkTable( fn x => hash(!x) , op = )
                                  ( 10000, DoNotPanic ))
      fun helper x = 
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
                                      * (helper succ )
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
                                      ( n + helper v ) 
                                      * ( helper succ )
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
      helper x
    end (* end fun paths *)

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  (* Export an SDD to a string *)
  fun toString x      =
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
