(*--------------------------------------------------------------------------*)
structure CacheConfiguration = struct

  datatype parameter = Name
                     | Buckets
                     | Threshold

  datatype result    = NameRes      of string
                     | BucketsRes   of int
                     | ThresholdRes of int

end

(*--------------------------------------------------------------------------*)
signature OPERATION = sig

  type operation
  type result

  val eq            : (operation * operation) -> bool
  val hash          : operation -> Hash.t

  val apply         : operation -> result

  val configure     :  CacheConfiguration.parameter
                       -> CacheConfiguration.result

end

(*--------------------------------------------------------------------------*)
