fun unionSDD alphaNodeToList alphaToList squareUnion commonApply 
             valUnion valDiff empty nodeAlpha 
             xs var
=
let

  val ( initial, operands ) = case map alphaNodeToList xs of
                                []       => raise DoNotPanic
                              | (y::ys)  => (y,ys)

  fun unionHelper ( lalpha, ralpha ) =
  let

    val commonPart = commonApply( lalpha, ralpha )

    fun diff xalpha yalpha =
    let
      val yUnion = valUnion( map (fn (x,_)=>x) yalpha )
    in
      foldl (fn ((xVal,xSuccs),acc) =>
              let
                val diff = valDiff(xVal,yUnion)
              in
                if empty diff then
                  acc
                else
                  ( diff, xSuccs )::acc
              end
            )
            []
            xalpha
    end

    val diffPartAB = diff lalpha ralpha
    val diffPartBA = diff ralpha lalpha

  in
    alphaToList ( squareUnion (diffPartAB @ commonPart @ diffPartBA) )
  end

  val alphaList = foldl unionHelper initial operands

  val l = map (fn (vl,succs) => case succs of
                                  s::[] => (vl,s)
                                | _     => raise DoNotPanic
              )
              alphaList

in
  nodeAlpha( var, Vector.fromList l )
end
