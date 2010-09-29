signature VALUATION =
sig

  type t

  val eq            : t * t -> bool
  val hash          : t -> Word32.word
  val length        : t -> int
  (* Must also remove duplicate elements *)
  val toString      : t -> string
  val union         : t * t -> t
  val intersection  : t * t -> t
  val difference    : t * t -> t

end
