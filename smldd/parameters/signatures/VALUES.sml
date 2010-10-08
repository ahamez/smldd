signature VALUATION =
sig

  type t

  val eq            : t * t -> bool
  val hash          : t -> Word32.word
  val length        : t -> int
  val empty         : t -> bool
  val mkEmpty       : unit -> t
  val union         : t * t -> t
  val intersection  : t * t -> t
  val difference    : t * t -> t
  val toString      : t -> string

end
