(* ------------------------------------------------------------------------ *)
structure SDD = SDDFun( structure Variable  = IntVariable
                      ; structure Values    = DiscreteIntValues )

structure Hom = HomFun( structure SDD      = SDD
                      ; structure Variable = IntVariable
                      ; structure Values   = DiscreteIntValues
                      )

structure IntOrder = OrderFun( structure Identifier = IntIdentifier
                             ; structure SDD        = SDD
                             ; structure Variable   = IntVariable
                             ; structure Values     = DiscreteIntValues
                             ; structure Hom        = Hom)

structure StringOrder = OrderFun( structure Identifier = StringIdentifier
                                ; structure SDD        = SDD
                                ; structure Variable   = IntVariable
                                ; structure Values     = DiscreteIntValues
                                ; structure Hom        = Hom)

structure Tools = ToolsFun( structure SDD      = SDD
                          ; structure Variable = IntVariable
                          ; structure Values   = DiscreteIntValues
                          ; structure Hom      = Hom
                          )

(* ------------------------------------------------------------------------ *)
structure BWSDD = SDDFun( structure Variable  = IntVariable
                        ; structure Values    = BitWordValues )

structure BWHom = HomFun( structure SDD      = BWSDD
                        ; structure Variable = IntVariable
                        ; structure Values   = BitWordValues
                        )

structure BWIntOrder = OrderFun( structure Identifier = IntIdentifier
                               ; structure SDD        = BWSDD
                               ; structure Variable   = IntVariable
                               ; structure Values     = BitWordValues
                               ; structure Hom        = BWHom)

structure BWStringOrder = OrderFun( structure Identifier = StringIdentifier
                                  ; structure SDD        = BWSDD
                                  ; structure Variable   = IntVariable
                                  ; structure Values     = BitWordValues
                                  ; structure Hom        = BWHom)

structure BWTools = ToolsFun( structure SDD      = BWSDD
                            ; structure Variable = IntVariable
                            ; structure Values   = BitWordValues
                            ; structure Hom      = BWHom
                            )

(* ------------------------------------------------------------------------ *)
