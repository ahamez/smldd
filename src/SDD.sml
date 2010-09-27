(*--------------------------------------------------------------------------*)

signature SDD =
sig
  
  type SDD
  type variable
  type valuation

  val zero          : SDD
  val one           : SDD
  val flat_node     : variable * valuation * SDD -> SDD
  val node          : variable * SDD * SDD -> SDD

  val union         : SDD list -> SDD
  val intersection  : SDD list -> SDD
  val difference    : SDD * SDD -> SDD

  val paths         : SDD -> int

  val toString      : SDD -> string
  val toDot         : SDD -> string

end

(*--------------------------------------------------------------------------*)

structure SDD =
struct

  (*----------------------------------------------------------------------*)

  structure Variable  : VARIABLE    = IntVariable
  structure Valuation : VALUATION   = DiscreteIntValuation

  (*----------------------------------------------------------------------*)

  structure SDD =
  struct
  
    datatype t    = SDD of ( sdd * Word32.word )
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
  
    fun hash (SDD(_,h)) = h
    
  end (* struct SDD *)
  open SDD

  (*----------------------------------------------------------------------*)

  (* Unicity *)
  structure ValUT = UnicityTableFun( structure Data = Valuation )
  structure SDDUT = UnicityTableFun( structure Data = SDD )

  (*----------------------------------------------------------------------*)

  exception IncompatibleSDD
  exception NotYetImplemented
  exception DoNotPanic (* Code 42 *)

  (*----------------------------------------------------------------------*)

  (* Return the |0| (zero) terminal *)
  val zero : SDD.t ref
    = SDDUT.unify( SDD( Zero , MLton.hash 0 ) )

  (*----------------------------------------------------------------------*)

  (* Return the |1| (one) terminal *)
  val one : SDD.t ref
    = SDDUT.unify( SDD( One  , MLton.hash 1 ) )

  (*----------------------------------------------------------------------*)

  (* Return a node with a set of discrete values on arc *)
  fun flat_node ( vr : Variable.t , values : Valuation.t , next : SDD.t ref )
                : SDD.t ref

    = case !next of
      SDD(Zero,_) => zero
    | _           =>
      if Valuation.length values = 0 then
        zero
      else
        let
          val sorted_values       = Valuation.sort_unique values
          val SDD(_,hash_next)    = !next
          val hash_values         = Valuation.hash sorted_values
          val h = Word32.xorb( MLton.hash vr
                             , Word32.xorb( hash_next, hash_values )
                             )
          val unik_values = ValUT.unify sorted_values
          val alpha = Vector.fromList [( unik_values, next )]
        in
          SDDUT.unify( SDD( Node{ variable=vr, alpha=alpha}, h) )
        end

  (*----------------------------------------------------------------------*)

  (* Return a node with a nested node on arc *)
  fun node  ( vr : Variable.t, nested : SDD.t ref , next : SDD.t ref )
            : SDD.t ref

    = case !next of
      SDD(Zero,_) => zero
    | _           =>
      case !nested of
        SDD(Zero,_) => zero
      | _           =>
        let
          val SDD(_,hash_next)    = !next
          val SDD(_,hash_nested)  = !nested
          val h = Word32.xorb( MLton.hash vr
                             , Word32.xorb( hash_next, hash_nested )
                             )
          val alpha = Vector.fromList [( nested, next )]
        in
          SDDUT.unify( SDD(HNode{ variable=vr, alpha=alpha}, h) )
        end

  (*----------------------------------------------------------------------*)

  (* Operations to manipulate SDD *)
  structure Op =
  struct
    
    type result        = SDD.t ref

    datatype operation = Union of
                            ( SDD.t ref list * (operation -> result) )
                       | Inter of 
                            ( SDD.t ref list * (operation -> result) )
                       | Diff  of
                            ( SDD.t ref * SDD.t ref * (operation -> result))
        
    (*------------------------------------------------------------*)
    fun union( [], _ )                    = zero
    |   union( (x::[]), _)                = x  
    |   union( (xs as (y::ys)), lookup)   =
    let
      (* Remove |0| *)
      val xs' = List.filter (fn x => case !x of 
                                        SDD(Zero,_) => false
                                      | _           => true
                            ) 
                            xs
      (* Check compatibility of operands *)
      val _ = foldl ( fn (x,y) => case !x of 
                                    SDD(One,_)  => 
                                      (case !y of
                                        SDD(One,_) => y
                                      | _ => raise IncompatibleSDD
                                      )
                                  | SDD(Node{...},_) =>
                                      (case !y of
                                        SDD(Node{...},_) => y
                                      | _ => raise IncompatibleSDD
                                      )
                                  | SDD(HNode{...},_) =>
                                      (case !y of
                                        SDD(HNode{...},_) => y
                                      | _ => raise IncompatibleSDD
                                      )
                                  (* Zero should have been filtered out *)
                                  | SDD(Zero,_) => raise DoNotPanic
    
                    )
                    y
                    xs'
    in
      zero
    end (* fun union *)
      
    (*------------------------------------------------------------*)
    fun intersection( [], _ )                   = zero
    |   intersection( (x::[]), _ )              = x
    |   intersection( (xs as (y::ys)), lookup)  =
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
      (* Check compatibility of operands *)
      fun check(x,xs) = foldl (fn (x,y) => case !x of 
                                    SDD(One,_)  => 
                                      (case !y of
                                        SDD(One,_) => y
                                      | _ => raise IncompatibleSDD
                                      )
                                  | SDD(Node{...},_) =>
                                      (case !y of
                                        SDD(Node{...},_) => y
                                      | _ => raise IncompatibleSDD
                                      )
                                  | SDD(HNode{...},_) =>
                                      (case !y of
                                        SDD(HNode{...},_) => y
                                      | _ => raise IncompatibleSDD
                                      )
                                  (* Zero should have been filtered out *)
                                  | SDD(Zero,_) => raise DoNotPanic
                              )
                              x
                              xs
    
    in
      (* Intersection with |0| is always |0| *)
      if has_zero then
        zero
      else
        check( y, ys);
        zero
    end (* fun intersection *) 
    
    (*------------------------------------------------------------*)
    fun difference( (l,r), lookup ) =
      if l = r then
        zero
      else
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
                raise NotYetImplemented
            )

        | SDD(HNode{variable=lvr,alpha=lalpha},_) =>
            raise NotYetImplemented
    (* fun difference *)

    (*------------------------------------------------------------*)

    (* Apply an SDD operation. Sort operands of union and intersection *)
    fun apply x =
      let
        fun qsort []       = []
        |   qsort (x::xs)  =
          let
            fun h x = let val SDD(_,res) = !x in res end
          in
             qsort (List.filter (fn y => (h y) < (h x) )  xs )
           @ [x]
           @ qsort (List.filter (fn y => (h y) >= (h x) ) xs )
          end
      in
        case x of
          Union(xs,lookup)  => union( qsort xs, lookup )
        | Inter(xs,lookup)  => intersection( qsort xs, lookup )
        | Diff(x,y,lookup)  => difference( (x,y), lookup)
      end
    
    (* Compute the hash value of an SDD operation *)
    fun hash x =
      let
        fun hash_operands( h0, xs ) = 
          foldl (fn(x,h) => Word32.xorb( SDD.hash(!x), h)) h0 xs
      in        
        case x of
          Union(xs,_)  => hash_operands( Word32.fromInt 15411567, xs)
        | Inter(xs,_ ) => hash_operands( Word32.fromInt 78995947, xs)
        | Diff(l,r,_)  => Word32.xorb( SDD.hash(!l), SDD.hash(!r) )
      end
    
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

    end (* struct Op *)

  (*----------------------------------------------------------------------*)

  (* Cache of operations on SDDs *)
  structure OpCache = CacheFun( structure Operation = Op )

  (* Let operations in Op call the cache *)
  val lookup_cache    = OpCache.lookup

  fun union xs        = OpCache.lookup(Op.Union( xs, lookup_cache ))
  fun intersection xs = OpCache.lookup(Op.Inter( xs, lookup_cache ))
  fun difference(x,y) = OpCache.lookup(Op.Diff( x, y, lookup_cache ))

  (*----------------------------------------------------------------------*)

  (* Count the number of distinct paths in a SDD *)
  fun paths x =
    let
      exception entry_not_found
      val cache : (( SDD.t ref , int ) HashTable.hash_table) ref
          = ref (HashTable.mkTable( fn x => SDD.hash(!x) , op = )
                                  ( 10000, entry_not_found ))
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
    end (* fun paths *)

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
    end (* fun toString *)

  (*----------------------------------------------------------------------*)

  (* Export an SDD to a DOT representation *)
  fun toDot _         = ""

  (*----------------------------------------------------------------------*)

end

(*--------------------------------------------------------------------------*)
