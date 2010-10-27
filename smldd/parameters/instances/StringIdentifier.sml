(*--------------------------------------------------------------------------*)
structure StringIdentifier = struct 

  type t = string

  val eq = op =
  val toString = Util.id

end (* structure StringIdentifier *)

(*--------------------------------------------------------------------------*)
