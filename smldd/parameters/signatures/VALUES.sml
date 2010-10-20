signature VALUES =
sig

  (* values view *)
  type values

  val hash            : values -> Hash.t
  val eq              : values * values -> bool
  val length          : values -> int
  val toString        : values -> string

  (* Library view *)
  eqtype stored
  eqtype value

  val discrete              : bool

  val storedToList          : stored -> value list
  val storedFromList        : value list -> stored

  val mkStorable            : values -> stored
  val mkUsable              : stored -> values

  val storedLt              : stored * stored -> bool
  val valueLt               : value * value -> bool

  val storedHash            : stored -> Hash.t

  val storedEmpty           : stored -> bool
  val storedMkEmpty         : unit -> stored

  val storedUnion           : stored list -> stored
  val storedIntersection    : stored list -> stored
  val storedDifference      : stored * stored -> stored

  val storedToString        : stored -> string

end
