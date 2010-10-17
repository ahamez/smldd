fun unionSDD alphaNodeToList alphaToList
             squareUnion commonApply
             valInter valDiff valEmpty
             nodeAlpha
             xs var
=
let

  val ( initial, operands ) = case map alphaNodeToList xs of
                                []       => raise DoNotPanic
                              | (y::ys)  => (y,ys)


  fun oneArcOfA a []
  = ( [a], [] )

  |   oneArcOfA (aVal,aSuccs) ((bVal,bSuccs)::bAlpha)
  =
    if aVal = bVal then
      ( [( aVal, aSuccs @ bSuccs )], bAlpha )

    else
    let
      val inter = valInter [aVal,bVal]
    in

      if valEmpty inter then
      let
        val (res,rem) = oneArcOfA (aVal,aSuccs) bAlpha
      in
        ( res, (bVal,bSuccs)::rem )
      end

      else (* inter not empty *)
      let
        val diffba = valDiff (bVal,aVal)
      in

        if aVal = inter then (* aVal \in bVal *)
          ( [( aVal, aSuccs @ bSuccs )], (diffba,bSuccs)::bAlpha )

        else
        let
          val diffab = valDiff (aVal,bVal)
        in
          if valEmpty diffba then
          let
            val (res,rem) = oneArcOfA (diffab,aSuccs) bAlpha
          in
            ( (inter, aSuccs @ bSuccs)::res, rem )
          end

          else
          let
            val (res,rem) = oneArcOfA (diffab,aSuccs) ((diffba,bSuccs)::bAlpha)
          in
            ( (inter, aSuccs @ bSuccs)::res, (diffba,bSuccs)::rem )
          end
        end
      end
    end

  fun partition ( [] , [] )    = []
  |   partition ( [], bAlpha ) = bAlpha
  |   partition ( aAlpha, [] ) = aAlpha
  |   partition ( a::aAlpha, bAlpha ) =
    let
      val (res,rem) = oneArcOfA a bAlpha
    in
      res @ (partition ( aAlpha, rem ))
    end

  val alpha = squareUnion (foldl partition initial operands)

in
  nodeAlpha( var, alpha )
end
