signature VALUES =
sig

  eqtype unique
  type plain

  val mkUnique      : plain -> unique
  val mkPlain       : unique -> plain

  val lt            : unique * unique -> bool

  val hash          : unique -> Hash.t

  val length        : unique -> int
  val empty         : unique -> bool
  val mkEmpty       : unit -> unique

  val union         : unique list -> unique
  val intersection  : unique list -> unique
  val difference    : unique * unique -> unique

  val toString      : unique -> string

end
