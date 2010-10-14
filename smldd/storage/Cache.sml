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

  structure W = MLton.Weak
  structure H = HashTable
  structure O = Operation

  type operation = O.operation
  type result    = O.result

  type wresult = result W.t

  exception entry_not_found

  val hits = ref 0
  val miss = ref 0
  val name = O.name

  fun stats () =
  let
    val total = (!miss) + (!hits)
    val rhits = Real.fromInt(!hits)
    val rmiss = Real.fromInt(!miss)
    val rtotal = Real.fromInt(total)
    val hrate = rhits / rtotal * 100.0
    val mrate = rmiss / rtotal * 100.0
  in
      "\n----------------------------\n"
    ^ "Cache " ^ name ^ "\n"
    ^ "hits  : " ^ (Int.toString (!hits)) ^ " | "
    ^ "miss  : " ^ (Int.toString (!miss)) ^ " | "
    ^ "total : " ^ (Int.toString (total)) ^ "\n"
    ^ "hits ratio : " ^ (Real.fmt (StringCvt.FIX (SOME 2)) hrate) ^"% | "
    ^ "miss ratio : " ^ (Real.fmt (StringCvt.FIX (SOME 2)) mrate) ^"%"
    ^ "\n"
  end

  val cache : ( operation , (wresult * int ref) ) H.hash_table
    = H.mkTable ( O.hash , O.eq ) ( 1000000, entry_not_found )

  fun lookup x =
  let

    fun cleanup () =
    let
      val _ = print ("\nCLEANUP " ^ name ^ "| before: ")
      val _ = print (Int.toString(H.numItems cache))
      val mean = Int.quot( (H.fold (fn ((_,hits),acc) => !hits + acc) 0 cache)
                         , (H.numItems cache)
                         )
      fun keep (v,hits) = case W.get v of
                            NONE    => false
                          | SOME _  => !hits > mean

      fun after () = (print (Int.toString(H.numItems cache)); print "\n")

      val _ = print "\n"
      val _ = print (stats())
      val _ = print " \n after: "
    in
(      H.filter keep cache;
      after()
)    end

    (* Cleanup cache *)
    val _ = if ( H.numItems cache ) > 1000000 then
              cleanup ()
            else
              ()

    fun store x =
      let
        val res  = O.apply x
        val wres = W.new res
      in
        H.insert cache ( x , (wres,ref 0) );
        valOf( W.get wres )
      end
  in

    case (H.find cache x) of
      SOME (r,h)  =>  (case W.get r of
                           SOME r' => (h := !h + 1;hits := !hits + 1;r')
                         | NONE    => ( miss := !miss + 1;
                                        H.remove cache x;
                                        store x
                                      )
                         )
    | NONE    =>  (miss := !miss + 1 ;store x)

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
