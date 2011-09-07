(* Should never happen: the |0| terminal has been encountered when
   traversing an SDD, meaning that the construction of SDDs is incorrect.
*)
exception ExplicitZero

(* Shoudl never happen: this exception describes all cases that should never
   arise. For instance, an empy list is encoutered whereas it should have been
   avoided by a calling function.
*)
exception DoNotPanic
