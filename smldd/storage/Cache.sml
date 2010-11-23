(*--------------------------------------------------------------------------*)

signature CACHE =
sig

  type operation
  type result

  val lookup : operation -> result

  val stats  : unit -> string

end

(*--------------------------------------------------------------------------*)
functor CacheFun ( structure Operation : OPERATION )
  : CACHE
= struct

  structure HT = HashTable
  structure W  = MLton.Weak
  structure O  = Operation
  structure C  = CacheConfiguration

  val name = let val C.NameRes n = O.configure C.Name in n end
             handle Match => ""

  val buckets = let val C.BucketsRes b = O.configure C.Buckets in b end
                handle Match => 1000000

  val threshold = let val C.ThresholdRes b = O.configure C.Threshold in b end
                  handle Match => 1000000


  type operation = O.operation
  type result    = O.result

  type wresult = result W.t

  val hits = ref 0
  val miss = ref 0

  val cache : ( operation , (wresult * int ref) ) HT.hash_table
    = HT.mkTable ( O.hash , O.eq ) ( buckets, Fail "Can't happen" )

  fun stats () =
  let
    val total = !miss + !hits
    val rhits = Real.fromInt(!hits)
    val rmiss = Real.fromInt(!miss)
    val rtotal = Real.fromInt(total)
    val hrate = rhits / rtotal * 100.0
    val mrate = rmiss / rtotal * 100.0
    val buckets = HT.bucketSizes cache
    val bucketMean = Real.fromInt((foldl (fn (x,acc) => x + acc) 0 buckets))
                     / Real.fromInt((length buckets))
  in
      "\n----------------------------\n"
    ^ "Cache " ^ name ^ "\n"
    ^ "hits  : " ^ (Int.toString (!hits)) ^ " | "
    ^ "miss  : " ^ (Int.toString (!miss)) ^ " | "
    ^ "total : " ^ (Int.toString (total)) ^ "\n"
    ^ "hits ratio : " ^ (Real.fmt (StringCvt.FIX (SOME 2)) hrate) ^"% | "
    ^ "miss ratio : " ^ (Real.fmt (StringCvt.FIX (SOME 2)) mrate) ^"%"
    ^ "\n\n"
    ^ "nb buckets : " ^ (Int.toString (length buckets)) ^ " | "
    ^ "bucketMean : " ^ (Real.fmt (StringCvt.FIX (SOME 5)) bucketMean)
    ^ "\n"
  end

  fun lookup x =
  let

    fun cleanup () =
    let
      val mean = Int.quot( HT.fold (fn ((_,hits),acc) => !hits + acc) 0 cache
                         , HT.numItems cache
                         )
      fun keep (v,hits) = case W.get v of
                            NONE    => false
                          | SOME _  => !hits > mean
    in
      HT.filter keep cache
    end

    (* Cleanup cache if necessary *)
    val _ = if ( HT.numItems cache ) > threshold then
              cleanup ()
            else
              ()

    fun store x =
      let
        val res   = O.apply x
        val wres  = W.new res
        val _     = HT.insert cache ( x , (wres,ref 0) );
      in
        res
      end
  in

    case (HT.find cache x) of
      SOME (r,h)  =>  (case W.get r of
                        SOME r' => ( h := !h + 1; hits := !hits + 1; r' )
                      | NONE    => ( miss := !miss + 1
                                   ; HT.remove cache x
                                   ; store x
                                   )
                      )
    | NONE    =>  ( miss := !miss + 1; store x )

  end

end (* CacheFun *)

(*--------------------------------------------------------------------------*)

functor NoCacheFun ( structure Operation : OPERATION )
  : CACHE
= struct

  structure O = Operation

  type operation = O.operation
  type result    = O.result

  fun lookup x = O.apply x

  fun stats () = ""

end (* NoCacheFun *)

(*--------------------------------------------------------------------------*)
