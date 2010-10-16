(*--------------------------------------------------------------------------*)

signature UnicityTable =
sig

  type data

  val unify  : data -> data ref

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

  val cleanup = ref 1000

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
      (* Remove weak pointers to nothing *)
      if (H.numItems values_table) > (!cleanup) then
      ( cleanup := !cleanup * 2;
        H.filter keep values_table
      )
      else
        ();

      case H.find values_table wrvalues of
        SOME v  =>  valOf(W.get v)
      | NONE    =>  ( H.insert values_table (wrvalues,wrvalues);
                      rvalues
                    )
    end

end (* UTFun *)

(*--------------------------------------------------------------------------*)

signature UnicityTableID =
sig

  type data

  val unify : (int -> data) -> data ref

end

(*--------------------------------------------------------------------------*)

functor UnicityTableFunID ( structure Data : DATA )
  : UnicityTableID
= struct

  structure W = MLton.Weak
  structure H = HashTable

  type data   = Data.t
  type wrdata = data ref MLton.Weak.t

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
  val values_table : ( wrdata, wrdata * int ) H.hash_table
    = H.mkTable ( hash, eq )
                ( 10000, data_not_found )

  val cleanup = ref 1000

  val id     = ref (case Int.minInt of
                     NONE   => 0
                   | SOME v => v
                   )
  val unused = ref []

  (* Return a ref to the unified valuation *)
  (* Values must be canonized before this unification *)
  fun unify mk =
    let
      val i = case !unused of
                []    => (id := !id + 1; !id)
              | x::xs => (unused := xs; x)
      val rvalues  = ref (mk i)
      val wrvalues = W.new rvalues
      (* Tell HashTable.filter which entries to keep *)
      fun keep (x,i) = case W.get x of
                         NONE    => ( unused := i :: (!unused);
                                      false
                                    )
                       | SOME _  => true
    in
      (* Remove weak pointers to nothing *)
      if (H.numItems values_table) > (!cleanup) then
      (
        cleanup := !cleanup * 2;
        H.filter keep values_table
      )
      else
        ();

      case H.find values_table wrvalues of
        SOME (v,_) => ( unused := i::(!unused) ; valOf(W.get v))
      | NONE       => ( H.insert values_table ( wrvalues, (wrvalues,i) );
                        rvalues
                      )
    end

end (* functor UnicityTableFunID *)

(*--------------------------------------------------------------------------*)
