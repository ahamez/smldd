signature VALUES =
sig

  (* Values view, e.g. what the user really works with *)
  type values

  val hash            : values -> Hash.t
  val eq              : values * values -> bool
  val length          : values -> int
  val empty           : values -> bool
  val toString        : values -> string
  val union           : values list -> values
  val intersection    : values list -> values

  (* Library view *)
  type stored
  eqtype value

  val discrete              : bool

  val storedToList          : stored -> value list
  val storedFromList        : value list -> stored

  val mkStorable            : values -> stored
  val mkUsable              : stored -> values

  val storedEq              : stored * stored -> bool
  val storedLt              : stored * stored -> bool
  val valueLt               : value * value -> bool

  val storedHash            : stored -> Hash.t

  val storedEmpty           : stored -> bool
  val storedUnion           : stored list -> stored
  val storedIntersection    : stored list -> stored
  val storedDifference      : stored * stored -> stored

  val storedToString        : stored -> string

end
