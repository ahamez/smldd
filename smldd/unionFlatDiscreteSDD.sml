fun unionFlatDiscreteSDD alphaNodeToList
                         vlToList vlFromList vlLt
                         valueLt
                         uid
                         unionSDD
                         nodeAlpha
                         xs var
=
let
  
  fun insertValue [] ( y , ysucc ) = [ (y, [ysucc]) ]
  |   insertValue (X as (( x, xsuccs )::xs)) ( y, ysucc ) =
    let

      fun insertSucc [] x = [x]
      |   insertSucc (L as (l::ls)) x =
        if x = l then
          L
        else if uid x < uid l then
          x::L
        else
          l::(insertSucc ls x)

    in
      if y = x then
        ( y, insertSucc xsuccs ysucc )::xs
      else if valueLt( y, x ) then
        ( y, [ysucc] )::X
      else
        ( x, xsuccs )::( insertValue xs ( y, ysucc ) )
    end

  fun insertVl acc (vl,succ::[]) =
    let
      fun helper ( value, acc ) = insertValue acc ( value, succ )
    in
      foldl helper acc (vlToList vl)
    end

  |   insertVl _ (_,_) = raise DoNotPanic

  fun insertAlpha ( [], acc ) = acc
  |   insertAlpha ( alpha, acc ) =
    let
      fun helper ( (vl,succs), acc ) = insertVl acc ( vl, succs )
    in
      foldl helper acc alpha
    end

  fun mergeSuccs ( ( value , succs  ) , acc ) =
  let

    val succ = unionSDD succs

    fun insert [] (succ,value) = [ (succ, [value]) ]
    |   insert (X as ((xsucc,xvls)::xs)) (succ,value) =
      if uid succ = uid xsucc then
        (* No need to sort xvls as we expect from vlFromList to
           do check and process its operands as needed
        *)
        ( succ, value::xvls )::xs
      else if uid succ < uid xsucc then
        ( succ, [value] )::X
      else
        (xsucc,xvls)::(insert xs (succ,value))

  in
    insert acc (succ,value)
  end

  fun mergeValues ( (succ,vls), acc ) =
  let

    val vl = vlFromList vls

    fun insert [] x = [x]
    |   insert (X as ((xvl,xsucc)::xs)) (vl,succ) =
      if vl = xvl then
        raise DoNotPanic
      else if vlLt( vl, xvl ) then
        (vl,succ)::X
      else
        (xvl,xsucc)::( insert xs (vl,succ) )

  in
    insert acc ( vl, succ )
  end

  val alpha   = foldl insertAlpha [] (map alphaNodeToList xs)  
  val alpha'  = foldl mergeSuccs  [] alpha
  val alpha'' = foldl mergeValues [] alpha'

in
  nodeAlpha( var, Vector.fromList alpha'' )
end