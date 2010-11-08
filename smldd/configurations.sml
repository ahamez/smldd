(* ------------------------------------------------------------------------ *)
structure SMLDD = SMLDDFun ( structure Identifier = IntIdentifier
                           ; structure Variable   = IntVariable
                           ; structure Values     = DiscreteIntValues
                           )

(* ------------------------------------------------------------------------ *)
structure BWSMLDD = SMLDDFun ( structure Identifier = IntIdentifier
                             ; structure Variable   = IntVariable
                             ; structure Values     = BitWordValues
                             )

(* ------------------------------------------------------------------------ *)
