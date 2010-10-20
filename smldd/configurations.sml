(* ------------------------------------------------------------------------ *)

structure SDD = SDDFun( structure Variable  = IntVariable
                      ; structure Values    = DiscreteIntValues )

structure Hom = HomFun( structure SDD      = SDD
                      ; structure Variable = IntVariable
                      ; structure Values   = DiscreteIntValues
                      )

structure Tools = ToolsFun( structure SDD      = SDD
                          ; structure Variable = IntVariable
                          ; structure Values   = DiscreteIntValues
                          )

(* ------------------------------------------------------------------------ *)

structure BoolSDD = SDDFun( structure Variable  = IntVariable
                          ; structure Values    = BooleanValues )

structure BoolHom = HomFun( structure SDD      = BoolSDD
                          ; structure Variable = IntVariable
                          ; structure Values   = BooleanValues
                          )

structure BoolTools = ToolsFun( structure SDD      = BoolSDD
                              ; structure Variable = IntVariable
                              ; structure Values   = BooleanValues
                              )

(* ------------------------------------------------------------------------ *)

structure BWSDD = SDDFun( structure Variable  = IntVariable
                        ; structure Values    = BitWordValues )

structure BWHom = HomFun( structure SDD      = BWSDD
                        ; structure Variable = IntVariable
                        ; structure Values   = BitWordValues
                        )

structure BWTools = ToolsFun( structure SDD      = BWSDD
                            ; structure Variable = IntVariable
                            ; structure Values   = BitWordValues
                            )

(* ------------------------------------------------------------------------ *)
