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

  structure W  = MLton.Weak
  structure HT = HashTable

  type data   = Data.t
  type wrdata = data ref MLton.Weak.t

  (* Hash a data *)
  val hash = Data.hash o ! o valOf o W.get

  (* Compare two datas *)
  fun eq ( l:wrdata, r:wrdata ) =
    case ( W.get l, W.get r ) of
      ( NONE, _ )       => false
    | ( _, NONE )       => false
    | ( SOME L, SOME R) => Data.eq( !L, !R )

  (* The type of the unicity table for valuations*)
  val values_table : ( wrdata, wrdata * int ) HT.hash_table
    = HT.mkTable ( hash, eq )
                ( 1000000, Fail "Can't happen" )

  val cleanup = ref 1000

  val id     = ref (case Int.minInt of NONE   => 0
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
      if HT.numItems values_table > !cleanup then
      (
        cleanup := !cleanup * 2;
        HT.filter keep values_table
      )
      else
        ();

      case HT.find values_table wrvalues of
        SOME (v,_) => ( unused := i::(!unused) ; valOf(W.get v))
      | NONE       => ( HT.insert values_table ( wrvalues, (wrvalues,i) );
                        rvalues
                      )
    end

end (* functor UnicityTableFunID *)

(*--------------------------------------------------------------------------*)
