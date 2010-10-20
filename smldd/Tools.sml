(*--------------------------------------------------------------------------*)
signature TOOLS = sig

  type SDD
  val nbPaths : SDD -> IntInf.int

end (* signature TOOLS *)

(*--------------------------------------------------------------------------*)
functor ToolsFun ( structure SDD : SDD
                   and Variable  : VARIABLE where type t    = SDD.variable
                   and Values    : VALUES   where type user = SDD.userValues
                 )
  : TOOLS
= struct

(*--------------------------------------------------------------------------*)
type SDD = SDD.SDD

(*--------------------------------------------------------------------------*)
(* Count the number of distinct paths in an SDD *)
fun nbPaths x =
let

  val visit = SDD.mkVisitor SDD.Cached

  fun zero () = IntInf.fromInt 0
  fun one  () = IntInf.fromInt 1

  fun node _ alpha =
    foldl (fn ( (vl,succ) , nb) =>
            case vl of
              SDD.Values v => nb +   (IntInf.fromInt (Values.usableLength v))
                                   * visit zero one node succ
            | SDD.Nested n => nb +   visit zero one node n
                                   * visit zero one node succ
          )
          (IntInf.fromInt 0)
          alpha

in
  visit zero one node x
end (* fun visitNbPaths *)

(*--------------------------------------------------------------------------*)
end (* fun ToolsFun *)
