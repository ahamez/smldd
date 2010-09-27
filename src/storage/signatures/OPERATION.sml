signature OPERATION =
sig

  type operation
  type result

  val eq            : (operation * operation) -> bool
  val hash          : operation -> Word32.word

  val apply         : operation -> result

  (*val toString      : operation -> string  *)
  (*val resToString   : result    -> string*)
  
end
