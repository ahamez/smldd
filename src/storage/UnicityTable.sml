(*--------------------------------------------------------------------------*)

signature UnicityTable =
sig
  
  type data
  type rdata  = data ref

  val unify : data -> rdata

end

(*--------------------------------------------------------------------------*)

functor UnicityTableFun ( structure Data : DATA )
  : UnicityTable
= struct

  structure W = MLton.Weak
  structure H = HashTable

  type data   = Data.t
  type rdata  = data ref
  type wrdata = rdata MLton.Weak.t

  (* Raised when a data is not found*)
  exception data_not_found

  (* Hash a data *)
  fun hash ( x:wrdata ) =
    let
      val unweak        = W.get x
      val unoption      = (valOf(unweak))
      val unref         = !unoption
      val hash          = Data.hash unref
    in
      hash
    end

  (* Compare two datas *)
  fun eq ( l:wrdata, r:wrdata ) =
    case W.get l of
      NONE    => false
    | SOME L  => case W.get r of
                    NONE   => false
                  | SOME R => Data.eq( !L, !R )

  (* The type of the unicity table for valuations*)
  val values_table : ( wrdata, wrdata ) H.hash_table
    = H.mkTable ( hash, eq )
                ( 10000, data_not_found )

  (* Return a ref to the unified valuation *)
  (* Values must be canonized before this unification *)
  fun unify ( values : data ) : rdata =
    let
      val rvalues  = ref values
      val wrvalues = W.new rvalues
      (* Tell HashTable.filter which entries to keep *)
      fun keep x = case W.get x of
                     NONE    => false
                   | SOME _  => true
    in
      if (H.numItems values_table) > 100000 then
        H.filter keep values_table
      else
        ();

      case H.find values_table wrvalues of
        SOME v  =>  valOf(W.get v)
      | NONE    =>  ( H.insert values_table (wrvalues,wrvalues);
                      valOf( W.get wrvalues )
                    )
    end

end (* UTFun *)

(*--------------------------------------------------------------------------*)
