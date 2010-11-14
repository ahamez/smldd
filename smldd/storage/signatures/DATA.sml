(*--------------------------------------------------------------------------*)
structure UnicityTableConfiguration = struct

  datatype parameter = Name
                     | Buckets
                     | CleanupStart
                     | CleanupFactor

  datatype result    = NameRes          of string
                     | BucketsRes       of int
                     | CleanupStartRes  of int
                     | CleanupFactorRes of int

end

(*--------------------------------------------------------------------------*)
signature DATA =
sig

  type t;

  val eq    : t * t -> bool
  val hash  : t -> Hash.t

  val configure : UnicityTableConfiguration.parameter
                  -> UnicityTableConfiguration.result

end

(*--------------------------------------------------------------------------*)
