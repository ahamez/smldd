(* Do the n-ary union of a list of SDDs' alphas.
   The general idea is to create a potential alpha
   of type ([values|SDD] * SDD list ) list which stores all
   successors for a given values set, which is then given to
   the square union function.

   In fact, it's not a real n-ary union as we operate on two operands
   at a time, the result becoming the 'bAlpha' operand on next iteration
   while 'aAlpha' is the head of the remaining operands (thus we use a
   foldl). 'bAlpha' is initialized by the alpha of the first operand.
*)
fun unionSDD uid valEq valInter valDiff valEmpty xs =
let

  fun mergeSuccs [] [] = []
  |   mergeSuccs xs [] = xs
  |   mergeSuccs [] ys = ys
  |   mergeSuccs (x::xs) ys =
    let
      fun mergeHelper acc [] x = x::acc
      |   mergeHelper acc (L as (l::ls)) x =
        if uid x = uid l then
          L @ acc
        else if uid x < uid l then
          x::(L @ acc)
        else
          mergeHelper (l::acc) ls x
    in
      rev( mergeSuccs xs (mergeHelper [] ys x) )
    end

  (* Process an arc of the a operand onto the whole alpha of b.
     When it's done, it returns a pair where the first element is the current
     alpha result, while the second element is what remains to be processed
     with the next arc of a.

     Successors list is constructed without removing duplicate elements
     ('aSuccs @ bSuccs') because sqaureUnion will remove these duplicates
     when it will create a union operation of these successors.
  *)
  fun oneArcOfA a [] = ( [a], [] )

  |   oneArcOfA (aVal,aSuccs) ((bVal,bSuccs)::bAlpha) =

    if valEq( aVal, bVal ) then
      ( [( aVal, mergeSuccs aSuccs bSuccs )], bAlpha )
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

        if valEq( aVal, inter ) then (* aVal \in bVal *)
          ( [( aVal, mergeSuccs aSuccs bSuccs )], (diffba,bSuccs)::bAlpha )

        else
        let
          val diffab = valDiff (aVal,bVal)
        in
          if valEmpty diffba then
          let
            val (res,rem) = oneArcOfA (diffab,aSuccs) bAlpha
          in
            ( (inter, mergeSuccs aSuccs bSuccs)::res, rem )
          end

          else
          let
            val (res,rem) = oneArcOfA (diffab,aSuccs) ((diffba,bSuccs)::bAlpha)
          in
            ( (inter, mergeSuccs aSuccs bSuccs)::res, rem )
          end
        end
      end
    end

  fun partition acc ( [] , [] )    = acc
  |   partition acc ( [], bAlpha ) = acc @ bAlpha
  |   partition acc ( aAlpha, [] ) = acc @ aAlpha
  |   partition acc ( a::aAlpha, bAlpha ) =
    let
      val (res,rem) = oneArcOfA a bAlpha
    in
      partition (acc@res) ( aAlpha, rem )
    end

  val (initial, operands) = case xs of []     => raise DoNotPanic
                                     | y::ys  => ( y, ys )

in
  foldl (partition []) initial operands
end
