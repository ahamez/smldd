structure TestHom =
struct

  (* ---------------------------------------------------------------- *)
  
  open Hom
  open SDD
  open SMLUnit.Assert
  structure Test = SMLUnit.Test

  (* ---------------------------------------------------------------- *)
  
  fun testId00 () =
    assertTrue( eval id one = one )

  (* ---------------------------------------------------------------- *)

  fun suite () =
      Test.labelTests
      [ ("testId00"          , testId00      )
      ]

  (* ---------------------------------------------------------------- *)

end
