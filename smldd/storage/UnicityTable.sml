(*--------------------------------------------------------------------------*)
signature UnicityTableID =
sig

  type data

  val unify : (int -> data) -> data

end

(*--------------------------------------------------------------------------*)
functor UnicityTableFunID ( structure Data : DATA )
  : UnicityTableID
= struct

  structure W  = MLton.Weak
  structure HT = HashTable
  structure C  = UnicityTableConfiguration
  structure D  = Data

  type data  = Data.t
  type wdata = data MLton.Weak.t

  val name =
    let val C.NameRes n = D.configure C.Name in n end
    handle Match => ""

  val buckets =
    let val C.BucketsRes b = D.configure C.Buckets in b end
    handle Match => 1000000

  val cleanup =
    ref (let val C.CleanupStartRes c = D.configure C.CleanupStart in c end
        handle Match => 1000000
        )

  val factor =
    let val C.CleanupFactorRes f = D.configure C.CleanupFactor in f end
    handle Match => 2

  (* Hash a data *)
  val hash = Data.hash o valOf o W.get

  (* Compare two datas *)
  fun eq ( l:wdata, r:wdata ) =
    case ( W.get l, W.get r ) of
      ( NONE, _ )       => false
    | ( _, NONE )       => false
    | ( SOME L, SOME R) => Data.eq( L, R )

  (* The type of the unicity table for valuations*)
  val values_table : ( wdata, int ) HT.hash_table
    = HT.mkTable ( hash, eq )
                ( buckets, Fail "Can't happen" )

  val id     = ref (case Int.minInt of NONE   => 0
                                     | SOME v => v
                   )
  val unused = ref []

  (* Return a ref to the unified valuation *)
  (* Values should be canonized before this unification *)
  fun unify mk =
    let
      val i = case !unused of
                []    => (id := !id + 1; !id)
              | x::xs => (unused := xs; x)
      val values  = mk i
      val wvalues = W.new values
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
        cleanup := !cleanup * factor;
        HT.filteri keep values_table
      )
      else
        ();

      case HT.findi values_table wvalues of
        SOME (v,_) => ( unused := i::(!unused) ; valOf(W.get v))
      | NONE       => ( HT.insert values_table ( wvalues, i );
                        values
                      )
    end

end (* functor UnicityTableFunID *)

(*--------------------------------------------------------------------------*)

