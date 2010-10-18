signature VALUES =
sig

  eqtype stored
  type user
  eqtype value

  val discrete      : bool
  val toList        : stored -> value list
  val fromList      : value list -> stored

  val mkStorable    : user -> stored
  val mkUsable      : stored -> user

  val lt            : stored * stored -> bool
  val valueLt       : value * value -> bool

  val hash          : stored -> Hash.t

  val length        : stored -> int
  val empty         : stored -> bool
  val mkEmpty       : unit -> stored

  val union         : stored list -> stored
  val intersection  : stored list -> stored
  val difference    : stored * stored -> stored

  val toString      : stored -> string

  val hashUsable    : user -> Hash.t
  val eqUsable      : user * user -> bool

end
