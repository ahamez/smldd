(*--------------------------------------------------------------------------*)

signature CACHE =
sig

  type operation
  type result

  val lookup : operation -> result

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

  val cache : ( operation , wresult ) H.hash_table
    = H.mkTable ( O.hash , O.eq )
                ( 100000, entry_not_found )

  fun lookup x =

    (
    if ( H.numItems cache ) > 100000 then
      let
        fun keep (k,v) = case W.get v of
                          NONE    => false
                        | SOME _  => true
      in
        H.filteri keep cache
      end
    else
      ();

    let

      fun store x =
        let
          val res  = O.apply x
          val wres = W.new res
        in
          H.insert cache ( x , wres );
          valOf( W.get wres )
        end
    in

      case (H.find cache x) of
        SOME r  =>  (
                    case W.get r of
                      SOME r' => r'
                    | NONE    => (
                                  H.remove cache x;
                                  store x
                                 )
                    )
      | NONE    =>  store x

    end
    )

end (* CacheFun *)

(*--------------------------------------------------------------------------*)
