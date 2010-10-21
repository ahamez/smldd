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
