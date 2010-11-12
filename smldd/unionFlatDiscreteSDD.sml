fun unionFlatDiscreteSDD vlToList vlFromList vlLt valueLt uid unionSDD xs =
let
  
  fun insertValue [] ( y , ysucc ) = [ (y, [ysucc]) ]
  |   insertValue (XS as ((X as ( x, xsuccs ))::xs)) (Y as ( y, ysucc )) =
    let

      fun insertSucc acc [] x = x::acc
      |   insertSucc acc (L as (l::ls)) x =
        if x = l then
          L @ acc
        else if uid x < uid l then
          x::(L@acc)
        else
          insertSucc (l::acc) ls x

    in
      if y = x then
        ( y, rev(insertSucc [] xsuccs ysucc) )::xs
      else if valueLt( y, x ) then
        ( y, [ysucc] )::XS
      else
        X::insertValue xs Y
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
    |   insert (XS as ((X as (xsucc,xvls))::xs)) (Y as (succ,value)) =
      if uid succ = uid xsucc then
        (* No need to sort xvls as we expect from vlFromList to
           do check and process its operands as needed
        *)
        ( succ, value::xvls )::xs
      else if uid succ < uid xsucc then
        ( succ, [value] )::XS
      else
        X::insert xs Y

  in
    insert acc (succ,value)
  end

  fun mergeValues ( (succ,vls), acc ) =
  let

    val vl = vlFromList vls

    fun insert [] x = [x]
    |   insert (XS as ((X as (xvl,xsucc))::xs)) (Y as (vl,succ)) =
      if vl = xvl then
        raise DoNotPanic
      else if vlLt( vl, xvl ) then
        Y::XS
      else
        X::insert xs Y

  in
    insert acc ( vl, succ )
  end

  val alpha   = foldl insertAlpha [] xs
  val alpha'  = foldl mergeSuccs  [] alpha
  val alpha'' = foldl mergeValues [] alpha'

in
  Vector.fromList alpha''
end