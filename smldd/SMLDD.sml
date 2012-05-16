(* ------------------------------------------------------------------------ *)
signature SMLDD = sig

  type variable
  type values

  structure Variable   : VARIABLE
  structure Values     : VALUES     where type values     = values
  structure SDD        : SDD        where type variable   = Variable.t
                                    where type values     = values
  structure Hom        : HOM        where type variable   = Variable.t
                                    where type values     = values
                                    where type SDD        = SDD.SDD
  structure Tools      : TOOLS      where type variable   = Variable.t
                                    where type values     = values
                                    where type SDD        = SDD.SDD
                                    where type hom        = Hom.hom

end (* signature SMLDD *)

(* ------------------------------------------------------------------------ *)
functor SMLDDFun ( structure Variable   : VARIABLE
                 ; structure Values     : VALUES
                 )
: SMLDD = struct

  type variable   = Variable.t
  type values     = Values.values

  structure Variable   = Variable
  structure Values     = Values

  structure SDD = SDDFun( structure Variable  = Variable
                        ; structure Values    = Values )

  structure Hom = HomFun( structure SDD      = SDD
                        ; structure Variable = Variable
                        ; structure Values   = Values
                        )

  structure Tools = ToolsFun( structure SDD      = SDD
                            ; structure Variable = Variable
                            ; structure Values   = Values
                            ; structure Hom      = Hom
                            )

end (* functor SMLDDFun *)

(* ------------------------------------------------------------------------ *)
