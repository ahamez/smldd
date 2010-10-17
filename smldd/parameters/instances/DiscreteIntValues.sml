structure DiscreteIntValues : VALUES =
struct

  structure SV = IntSortedVector
  structure H  = Hash
  structure HT = HashTable

  type unique = SV.t ref
  type plain  = SV.t

  structure UT = UnicityTableFun ( structure Data = IntSortedVector )

  val mkUnique = UT.unify
  val mkPlain  = !

  fun lt (x,y) = SV.lt( !x, !y)
  val hash     = SV.hash o !
  val length   = SV.length o !
  val empty    = SV.empty o !
  val toString = SV.toString o !

  val e = UT.unify (SV.mkEmpty())
  fun mkEmpty() = e

  local

    (* Operations to manipulate values. Used by the cache. *)
    structure Operations (* : OPERATION *) =
    struct

      val name = "Values"

      type result        = unique
      datatype operation = Union of unique list
                         | Inter of unique list
                         | Diff  of unique * unique

      fun eq (l,r) =
        case (l,r) of
          ( Union(xs), Union(ys) )     => xs = ys
        | ( Inter(xs), Inter(ys) )     => xs = ys
        | ( Diff(lx,ly), Diff(rx,ry) ) => lx = rx andalso ly = ry
        | ( _, _ )                     => false

      fun hash x =
        let
          (* Values.hash(!x) -> problem: we have to compute again
             the hash value of the valuation... Maybe we should store
             this hash alongside of the valuation? *)
          fun hashOperands( h0, xs ) =
            foldl (fn(x,h) => H.hashCombine( SV.hash(!x), h)) h0 xs
        in
          case x of
            Union(xs) => hashOperands( H.const 15411567, xs)
          | Inter(xs) => hashOperands( H.const 78995947, xs)
          | Diff(l,r) => H.hashCombine( H.const 94165961
                                      , H.hashCombine( SV.hash(!l)
                                                     , SV.hash(!r))
                                      )
        end

      (* Evaluation an operation on valuations. Called by CacheFun. *)
      fun apply operation =

        case operation of

          Union []     => raise DoNotPanic
        | Union(x::xs) =>
            UT.unify(foldl ( fn (x,res) => SV.union(!x,res) )
                              (!x)
                              xs
                        )

        | Inter []     => raise DoNotPanic
        | Inter(x::xs) =>
            UT.unify(foldl ( fn (x,res) => SV.intersection(!x,res) )
                              (!x)
                              xs
                        )

        | Diff(x,y)    => UT.unify( SV.difference( !x, !y) )

    end (* end structure Operations *)

  in (* local *)

    (* Cache of operations *)
    structure cache = CacheFun(structure Operation = Operations )

    val sortValues = sortUnique ! (SV.lt) (fn (x,y) =>
                                            not (SV.lt(x,y))
                                            andalso not (SV.eq(x,y))
                                          )

    fun union xs =
      case sortValues xs of
        []      => raise DoNotPanic
      | (x::[]) => x (* No need to cache *)
      | _       => cache.lookup( Operations.Union xs )

    fun intersection xs =
      case sortValues xs of
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
