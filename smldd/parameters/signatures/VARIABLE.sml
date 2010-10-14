signature VARIABLE =
sig

  type t

  val eq        : t * t -> bool
  val hash      : t -> Hash.t
  val toString  : t -> string

end
