signature VALUES =
sig

  type t

  val eq            : t * t -> bool
  val lt            : t * t -> bool

  val hash          : t -> Hash.t

  (*val unify         : t -> t*)

  val length        : t -> int
  val empty         : t -> bool
  val mkEmpty       : unit -> t

  (*val union         : t list -> t
  val intersection  : t list -> t*)
  val union         : t * t -> t
  val intersection  : t * t -> t
  val difference    : t * t -> t

  val toString      : t -> string

end
