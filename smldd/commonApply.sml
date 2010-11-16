fun commonApply valInter valEmpty cont empty ( aAlpha, bAlpha ) =
let

  fun propagate acc ( _, [] ) =  acc
  |   propagate acc ( aArc as (aVal,aSuccs), (bVal,bSuccs)::bAlpha ) =
  let
    val inter = valInter [aVal,bVal]
  in
    if valEmpty inter then
      propagate acc ( aArc, bAlpha)
    else
      let
        val succ = cont (aSuccs@bSuccs)
      in
        if empty succ then
          propagate acc ( aArc, bAlpha )
        else
          propagate ( (inter,[succ])::acc ) ( aArc, bAlpha)
      end
  end

  fun helper acc ( [], _ ) = acc
  |   helper acc ( aArc::aAlpha, bAlpha ) =
  let
    val acc' = (propagate [] ( aArc, bAlpha ) )@acc
  in
    helper acc' ( aAlpha, bAlpha )
  end

in
  helper [] ( aAlpha, bAlpha )
end
