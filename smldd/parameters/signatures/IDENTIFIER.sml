(*--------------------------------------------------------------------------*)
signature IDENTIFIER = sig

  eqtype t

  val eq       : t * t -> bool
  val toString : t -> string

end (* signature IDENTIFIER *)

(*--------------------------------------------------------------------------*)
