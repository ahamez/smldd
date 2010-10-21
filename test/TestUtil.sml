structure TestUtil =
struct

  open Util
  open SMLUnit.Assert
  structure Test = SMLUnit.Test

  fun testShuffle00 () =
  let
    val l = List.tabulate (100, Util.id)
    val r = shuffle l
    val _ = print ("[" ^ (String.concatWith "," (map Int.toString r)) ^ "]")
  in
    assertTrue( l <> r )
  end

  fun suite () =
      Test.labelTests
      [ ("testShuffle00"     , testShuffle00   )
      ]

end
