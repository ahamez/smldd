(*--------------------------------------------------------------------------*)
signature ORDER = sig

  type identifier
  type variable
  type values
  type SDD
  type hom

  type order

  val eq                   : order * order -> bool

  val mkOrder              : unit -> order
  val flatOrder            : identifier list -> order
  val addFlatNode          : order -> identifier -> order
  val addHierarchicalNode  : order -> identifier -> order -> order
  val concat               : order list -> order

  datatype mode            = Anonymise
                           | Flatten
                           | MaxLeaves of int
                           | Shuffle
                           | Id

  val transform            : mode -> order -> order

  val SDD                  : order -> (identifier -> values) -> SDD
  val hom                  : order -> identifier -> (variable -> hom) -> hom

  val toString             : order -> string

  exception ArtificialNode

end (* signature ORDER *)

(*--------------------------------------------------------------------------*)
functor OrderFun ( structure Identifier : IDENTIFIER
                 ; structure SDD : SDD
                   and Variable  : VARIABLE where type t = SDD.variable
                   and Values    : VALUES   where type values = SDD.values
                   and Hom       : HOM      where type SDD = SDD.SDD
                                            where type variable = SDD.variable
                                            where type values = SDD.values
                 )
  : ORDER = struct

(*--------------------------------------------------------------------------*)
exception ArtificialNode

(*--------------------------------------------------------------------------*)
type identifier = Identifier.t
type variable   = Variable.t
type values     = Values.values
type SDD        = SDD.SDD
type hom        = Hom.hom

(*--------------------------------------------------------------------------*)
datatype node  = Node of ( variable * identifier option )
datatype order = Order of (node * order option) list

(*--------------------------------------------------------------------------*)
fun eqNode ( Node(v,i), Node(w,j) ) =
  Variable.eq(v,w) andalso i = j

(*--------------------------------------------------------------------------*)
fun eq ( Order xs, Order ys ) =
let
  fun helper [] [] = true
  |   helper _  [] = false
  |   helper [] _  = false
  |   helper ((nx,nestedOrdx)::xs) ((ny,nestedOrdy)::ys) =
    eqNode( nx, ny ) andalso helper xs ys
                     andalso case ( nestedOrdx, nestedOrdy ) of
                               ( NONE, NONE )   => true
                             | ( NONE, _ )      => false
                             | ( _, NONE )      => false
                             | (SOME x, SOME y) => eq(x,y)
in
  helper xs ys
end

(*--------------------------------------------------------------------------*)
fun variable   (Node( v, _ )) = v

fun nodes (Order ns) = ns

(*--------------------------------------------------------------------------*)
fun nextVar (Order [] )       = Variable.first
|   nextVar (Order((n,_)::_)) = Variable.next (variable n)

(*--------------------------------------------------------------------------*)
fun mkOrder () = Order []

(*--------------------------------------------------------------------------*)
fun addFlatNode' (Order []) n = Order [( n, NONE )]
|   addFlatNode' (Order ns) n = Order (( n, NONE )::ns)

(*--------------------------------------------------------------------------*)
fun addFlatNode ord i =
  addFlatNode' ord (Node ( nextVar ord, SOME i ))

(*--------------------------------------------------------------------------*)
fun flatOrder [] = Order []
|   flatOrder is = foldr (fn (i,acc) => addFlatNode acc i) (Order []) is

(*--------------------------------------------------------------------------*)
fun concat xs =
  foldr (fn ( Order x, Order acc) => Order (x @ acc)) (mkOrder ()) xs

(*--------------------------------------------------------------------------*)
fun addHierarchicalNode' (Order []) n nestedOrd =
  Order [( n, SOME nestedOrd )]

|   addHierarchicalNode' (Order ns ) n nestedOrd =
  Order (( n, SOME nestedOrd )::ns)

(*--------------------------------------------------------------------------*)
fun addHierarchicalNode ord i nestedOrd =
  addHierarchicalNode' ord (Node ( nextVar ord, SOME i )) nestedOrd

(*--------------------------------------------------------------------------*)
datatype mode = Anonymise
              | Flatten
              | MaxLeaves of int
              | Shuffle
              | Id

(*--------------------------------------------------------------------------*)
fun transform _ (Order []) = Order []

(*--------------------------------------------------------------------------*)
|   transform Anonymise (Order ns) =
let
  fun helper ( (Node(_,i), NONE), acc) =
    addFlatNode' acc ( Node( nextVar acc, i ) )

  |   helper ( (Node(_,i), SOME nested), acc) =
    addHierarchicalNode' acc
                         ( Node( nextVar acc, i ) ) 
                         (transform Anonymise nested)
    
in
  foldr helper (mkOrder ()) ns
end

(*--------------------------------------------------------------------------*)
|   transform Flatten (Order ns) =
let
  fun helper ( ( Node(_,i), NONE ), acc ) =
    addFlatNode' acc ( Node( nextVar acc, i ) )

  |   helper ( ( _, SOME nested ), acc ) =
    foldr (fn ((Node(_,i),_),acc) =>
            addFlatNode' acc ( Node( nextVar acc, i ) )
          )
          acc
          (nodes (transform Flatten nested))
in
  foldr helper (mkOrder ()) ns
end

(*--------------------------------------------------------------------------*)
|   transform (MaxLeaves 0) _ = raise Domain
|   transform (MaxLeaves 1) _ = raise Domain
|   transform (MaxLeaves leaves) (Order ns) =
  if length ns < leaves then
    Order ns
  else
  let

    fun helper ns =
    let
      val packets  = Util.explodeRightBy ns leaves
      val packets' = map (fn x => Order x) packets
    in
      foldr (fn (x,acc) =>
              addHierarchicalNode' acc (Node( nextVar acc, NONE )) x
            )
            (mkOrder ())
            packets'
    end

  in
    transform (MaxLeaves leaves) (helper ns)
  end

(*--------------------------------------------------------------------------*)
|   transform Shuffle (Order ns) =
let
  fun helper ( (Node(v,i), NONE), acc) =
    addFlatNode' acc ( Node( v, i ) )

  |   helper ( (Node(v,i), SOME nested), acc) =
    addHierarchicalNode' acc
                         ( Node( v, i ) )
                         (transform Shuffle nested)

in
  foldr helper (mkOrder ()) (Util.shuffle ns)
end

(*--------------------------------------------------------------------------*)
|   transform Id ord = ord

(*--------------------------------------------------------------------------*)
fun SDD (Order ns) f =
let

  fun helper ( (Node(v,i), NONE), acc ) =
    (SDD.node( v, SDD.Values (f (valOf i)), acc )
    handle Option => raise ArtificialNode)
  
  |   helper ( (Node(v,_), SOME nested), acc ) =
    SDD.node( v, SDD.Nested (SDD nested f), acc )

in
  foldr helper SDD.one ns
end

(*--------------------------------------------------------------------------*)
fun hom (Order ns) i mk =
let

  fun helper [] = NONE

  |   helper ( (Node(_,NONE), NONE )::ns ) =
    helper ns

  |   helper ( (Node(v,NONE), SOME (Order nested) )::ns ) =
    (case helper nested of
      NONE   => helper ns
    | SOME x => SOME (Hom.mkNested x v)
    )

  |   helper ( (Node(v,SOME j), _ )::ns ) =
    if Identifier.eq( i, j ) then
      SOME (mk v)
    else
      helper ns

in
  case helper ns of
    NONE   => Hom.id
  | SOME x => x
end

(*--------------------------------------------------------------------------*)
fun toString (Order ns) =
let
  
  fun indent i = String.concat (List.tabulate (i,(fn _ => " ")))
  
  fun helper _ [] = ""

  |   helper spaces ( (Node(v,i), nested )::ns ) =
    (indent spaces)
  ^ "["
  ^ (Variable.toString v)
  ^ (case i of NONE   => ""
             | SOME x => " <-> " ^ (Identifier.toString x)
    )
  ^ "]\n"
  ^ (case nested of NONE           => ""
                  | SOME (Order x) => (helper (spaces+4) x)
    )
  ^ (helper spaces ns)

in
  helper 0 ns
end

(*--------------------------------------------------------------------------*)
end (* functor OrderFun *)
