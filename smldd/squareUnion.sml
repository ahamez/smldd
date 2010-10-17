(* Merge all values that lead to the same successor.
   It returns an alpha suitable to build a new node with
   nodeAlpha.

   alpha : ( (values'|SDD) * SDD list ) list
     -> ( values' * SDD ) Vector.vector

*)
fun squareUnion uid SDDUnion valUnion valLt alpha =
let

  fun mergeSuccs ( ( vl , succs  ) , acc ) =
  let

    val succ = SDDUnion succs

    fun insert [] (succ,vl) = [ (succ, [vl]) ]
    |   insert (X as ((xsucc,xvls)::xs)) (succ,vl) =
      if uid succ = uid xsucc then
        ( succ, vl::xvls )::xs
      else if uid succ < uid xsucc then
        ( succ, [vl] )::X
      else
        (xsucc,xvls)::(insert xs (succ,vl))

  in
    insert acc (succ,vl)
  end


  fun mergeVls ( (succ,vls), acc ) =
  let

    val vl = valUnion vls

    fun insert [] x = [x]
    |   insert (X as ((xvl,xsucc)::xs)) (vl,succ) =
      if vl = xvl then
        raise DoNotPanic
      else if valLt( vl, xvl ) then
        (vl,succ)::X
      else
        (xvl,xsucc)::( insert xs (vl,succ) )

  in
    insert acc ( vl, succ )
  end
  
  val alpha'  = foldl mergeSuccs [] alpha
  val alpha'' = foldl mergeVls   [] alpha'

in
  Vector.fromList (alpha'')
end
