signature VARIABLE =
sig

  type t

  val eq        : t * t -> bool
  val lt        : t * t -> bool
  val hash      : t -> Hash.t
  val toString  : t -> string

  val first     : t
  val next      : t -> t

end
