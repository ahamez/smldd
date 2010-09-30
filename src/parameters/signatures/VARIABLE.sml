signature VARIABLE =
sig

  type t

  val eq        : t * t -> bool
  val lt        : t * t -> bool
  val hash      : t -> Word32.word
  val toString  : t -> string

end
