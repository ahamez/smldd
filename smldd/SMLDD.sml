(* ------------------------------------------------------------------------ *)
signature SMLDD = sig

  eqtype identifier
  type variable
  type values

  structure Identifier : IDENTIFIER where type t          = identifier
  structure Variable   : VARIABLE
  structure Values     : VALUES     where type values     = values
  structure SDD        : SDD        where type variable   = Variable.t
                                    where type values     = values
  structure Hom        : HOM        where type variable   = Variable.t
                                    where type values     = values
                                    where type SDD        = SDD.SDD
  structure Order      : ORDER      where type identifier = identifier
                                    where type variable   = Variable.t
                                    where type values     = values
                                    where type SDD        = SDD.SDD
                                    where type hom        = Hom.hom
  structure Tools      : TOOLS      where type identifier = identifier
                                    where type variable   = Variable.t
                                    where type values     = values
                                    where type SDD        = SDD.SDD
                                    where type hom        = Hom.hom
                                    where type order      = Order.order

end (* signature SMLDD *)

(* ------------------------------------------------------------------------ *)

functor SMLDDFun ( structure Identifier : IDENTIFIER
                 ; structure Variable   : VARIABLE
                 ; structure Values     : VALUES
                 )
: SMLDD = struct

  type identifier = Identifier.t
  type variable   = Variable.t
  type values     = Values.values

  structure Identifier = Identifier
  structure Variable   = Variable
  structure Values     = Values

  structure SDD = SDDFun( structure Variable  = Variable
                        ; structure Values    = Values )

  structure Hom = HomFun( structure SDD      = SDD
                        ; structure Variable = Variable
                        ; structure Values   = Values
                        )

  structure Order = OrderFun( structure Identifier = Identifier
                            ; structure SDD        = SDD
                            ; structure Variable   = Variable
                            ; structure Values     = Values
                            ; structure Hom        = Hom
                            )

  structure Tools = ToolsFun( structure SDD      = SDD
                            ; structure Variable = Variable
                            ; structure Values   = Values
                            ; structure Hom      = Hom
                            ; structure Order    = Order
                            )

end (* functor SMLDDFun *)
