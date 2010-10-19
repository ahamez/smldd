structure DiscreteIntValues : VALUES =
struct

  structure SV = IntSortedVector
  structure H  = Hash
  structure HT = HashTable

  structure Definition = struct

    type t = ( SV.t * H.t * int )

    fun eq   ((x,_,_),(y,_,_)) = SV.eq(x,y)
    fun hash (x,_,_) = SV.hash x

  end

  val discrete = true

  type stored = Definition.t ref
  type user   = SV.t
  type value  = int


  structure UT = UnicityTableFunID ( structure Data = Definition )

  fun uid (ref(_,_,x)) = x
  fun mkValues v hsh uid = ( v, hsh, uid )

  fun mkStorable v        = UT.unify (mkValues v (SV.hash v))
  fun mkUsable (ref(v,_,_)) = v

  fun toList (ref(v,_,_)) = Util.IntVectorToList v
  fun fromList xs =
  let
    val v = (SV.fromList xs)
  in
    UT.unify ( mkValues v (SV.hash v) )
  end

  val valueLt  = (op <)

  fun lt (x,y)               = uid x < uid y
  fun hash (ref(x,_,_))      = SV.hash x
  fun length (ref(x,_,_))    = SV.length x
  fun empty (ref(x,_,_))     = SV.empty x
  fun toString (ref(x,_,_))  = SV.toString x

  val hashUsable = SV.hash
  val eqUsable   = SV.eq

  val e = mkStorable( SV.mkEmpty() )
  fun mkEmpty() = e

  local

    (* Operations to manipulate values. Used by the cache. *)
    structure Operations (* : OPERATION *) =
    struct

      val name = "Values"

      type result        = stored
      datatype operation = Union of stored list
                         | Inter of stored list
                         | Diff  of stored * stored

      fun eq (l,r) =
        case (l,r) of
          ( Union(xs), Union(ys) )     => xs = ys
        | ( Inter(xs), Inter(ys) )     => xs = ys
        | ( Diff(lx,ly), Diff(rx,ry) ) => lx = rx andalso ly = ry
        | ( _, _ )                     => false

      fun hash x =
        let
          fun hashOperands( h0, xs ) =
            foldl (fn ( ref(_,hv,_), h ) => H.hashCombine( hv, h)) h0 xs
        in
          case x of
            Union(xs) => hashOperands( H.const 15411567, xs)
          | Inter(xs) => hashOperands( H.const 78995947, xs)
          | Diff(ref(l,hl,_),ref(r,hr,_)) =>
              H.hashCombine( H.const 94165961
                           , H.hashCombine( hl, hr )
                           )
        end

      (* Evaluation an operation on valuations. Called by CacheFun. *)
      fun apply operation =

        case operation of

          Union []     => raise DoNotPanic
        | Union(ref(x,_,_)::xs) =>
            let
              val v   = foldl (fn (ref(v,_,_),res) => SV.union(v,res)) x xs
              val hsh = SV.hash v
            in
              UT.unify (mkValues v hsh)
            end

        | Inter []     => raise DoNotPanic
        | Inter(ref(x,_,_)::xs) =>
            let
              val v = foldl (fn (ref(v,_,_),res) => SV.intersection(v,res))
                            x xs
              val hsh = SV.hash v
            in
              UT.unify (mkValues v hsh)
            end

        | Diff( ref(l,_,_), ref(r,_,_) ) =>
            let
              val v   = SV.difference( l, r )
              val hsh = SV.hash v
            in
              UT.unify (mkValues v hsh)
            end

    end (* end structure Operations *)

  in (* local *)

    (* Cache of operations *)
    structure cache = CacheFun(structure Operation = Operations )

    (* Operands should be sorted by caller *)
    fun union xs =
      case xs of
        []      => raise DoNotPanic
      | (x::[]) => x (* No need to cache *)
      | _       => cache.lookup( Operations.Union xs )

    (* Operands should be sorted by caller *)
    fun intersection xs =
      case xs of
        []      => raise DoNotPanic
      | (x::[]) => x (* No need to cache *)
      | _       => cache.lookup( Operations.Inter xs )

    fun difference(x,y) =
      if x = y then
        mkEmpty()
      else
        cache.lookup( Operations.Diff(x,y) )

    val stats = cache.stats

  end (* local *)

end (* DiscreteIntValues *)
