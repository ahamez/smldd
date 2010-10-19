structure BooleanValues : VALUES =
struct

structure H  = Hash

(* Different possible sets are encoded as follow:
   {}    => 0
   {0}   => 1
   {1}   => 2
   {0,1} => 3
*)

val discrete = true

type value  = int

fun toList v   = case v of
                   0 => []
                 | 1 => [0]
                 | 2 => [1]
                 | 3 => [0,1]
                 | _ => (print (Int.toString v);raise DoNotPanic)

fun fromList xs =
  case ( List.exists (fn x => x = 0) xs, List.exists (fn x => x = 1) xs ) of
    ( false, false ) => 0
  | ( true , false ) => 1
  | ( false, true  ) => 2
  | ( true , true  ) => 3

val valueLt = op <

type stored = int
type user   = int

val mkStorable = Util.id
val mkUsable   = Util.id

val lt =  op <
val hash = H.const
fun length x = case x of
                 0 => 0
               | 1 => 1
               | 2 => 1
               | 3 => 2
               | _ => raise DoNotPanic

fun empty x = x = 0

fun toString x = case x of
                   0 => "{}"
                 | 1 => "{0}"
                 | 2 => "{1}"
                 | 3 => "{0,1}"
                 | _ => raise DoNotPanic

fun mkEmpty () = 0

val hashUsable = H.const
val eqUsable   = (op =)

fun union []      = 0
|   union (x::[]) = x
|   union (x::xs) =
let
  fun unionHelper (x,y) =
    case (x,y) of
      (0,_) => y
    | (_,0) => x
    | (3,_) => 3
    | (_,3) => 3
    | (1,2) => 3
    | (2,1) => 3
    | (_,_) => x
in
  foldl unionHelper x xs
end

fun intersection []      = 0
|   intersection (x::[]) = x
|   intersection (x::xs) =
let
  fun interHelper (x,y) =
    case (x,y) of
      (0,_) => 0
    | (_,0) => 0
    | (1,2) => 0
    | (2,1) => 0
    | (3,_) => y
    | (_,3) => x
    | (_,_) => x
in
  foldl interHelper x xs
end

fun difference(x,y) =
  case (x,y) of

    (0,_) => 0
  | (_,0) => x

  | (_,3) => 0

  | (1,2) => 1

  | (2,1) => 2

  | (3,1) => 2
  | (3,2) => 1

  | (_,_) => 0

end (* BooleanValues *)
