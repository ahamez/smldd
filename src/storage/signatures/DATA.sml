signature DATA =
sig

  type t;

  val eq    : t * t -> bool
  val hash  : t -> Word32.word

end
