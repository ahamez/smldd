(* ------------------------------------------------------------------------ *)

structure SDD = SDDFun( structure Variable  = IntVariable
                      ; structure Values    = DiscreteIntValues )

structure Hom = HomFun( structure SDD      = SDD
                      ; structure Variable = IntVariable
                      ; structure Values   = DiscreteIntValues
                      )

(* ------------------------------------------------------------------------ *)

(*structure BoolSDD = SDDFun( structure Variable  = IntVariable
                          ; structure Values    = BooleanValues )

structure BoolHom = HomFun( structure SDD      = BoolSDD
                          ; structure Variable = IntVariable
                          ; structure Values   = BooleanValues
                          )*)

(* ------------------------------------------------------------------------ *)
