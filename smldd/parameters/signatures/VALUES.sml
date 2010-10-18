signature VALUES =
sig

  eqtype stored
  type user

  val mkStorable    : user -> stored
  val mkUsable      : stored -> user

  val lt            : stored * stored -> bool

  val hash          : stored -> Hash.t

  val length        : stored -> int
  val empty         : stored -> bool
  val mkEmpty       : unit -> stored

  val union         : stored list -> stored
  val intersection  : stored list -> stored
  val difference    : stored * stored -> stored

  val toString      : stored -> string

end
