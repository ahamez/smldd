fun commonApply _ _ _ _ ( [], _ ) = []
|   commonApply valInter valEmpty cont zero ( aArc::aAlpha, bAlpha ) =
let

  fun propagate ( _, [] ) =  []
  |   propagate ( aArc as (aVal,aSuccs), (bVal,bSuccs)::bAlpha ) =
  let
    val inter = valInter [aVal,bVal]
  in
    if valEmpty inter then
      propagate ( aArc, bAlpha)
    else
      let
        val succ = cont (aSuccs@bSuccs)
      in
        if succ = zero then
          propagate ( aArc, bAlpha )
        else
          ( inter, [succ] ) :: propagate ( aArc, bAlpha)
      end
  end

in
    propagate ( aArc, bAlpha  )
  @ commonApply valInter valEmpty cont zero ( aAlpha, bAlpha )
end
