(*--------------------------------------------------------------------------*)
signature HOM = sig

  type hom
  type SDD
  type variable
  type values
  type valuation

  val eq                : hom * hom -> bool
  val uid               : hom -> int

  val id                : hom
  val zero              : hom
  val one               : hom
  val mkCons            : variable -> valuation -> hom -> hom
  val mkConst           : SDD -> hom
  val mkUnion           : hom list -> hom
  val mkIntersection    : hom list -> hom
  val mkComposition     : hom -> hom -> hom
  val mkFixpoint        : hom -> hom
  val mkNested          : hom -> variable -> hom

  type context
  val emptyContext      : context
  val isEmptyContext    : context -> bool
  val mergeContexts     : context list -> context
  val intersectContexts : context list -> context
  val addValues         : context -> variable -> values -> context
  val removeVariable    : context -> variable -> context
  val eqContext         : context * context -> bool

  datatype UserIn       = FuncValues of (context * values)
                        | InductiveSkip of variable
                        | InductiveValues of (context * variable * values)
                        | InductiveOne
                        | Selector
                        | Hash
                        | Print

  datatype UserOut      = FuncValuesRes of (context * values)
                        | InductiveSkipRes of bool
                        | InductiveValuesRes of (context * hom)
                        | InductiveOneRes of SDD
                        | SelectorRes of bool
                        | HashRes of Hash.t
                        | PrintRes of string

  type user             = (UserIn -> UserOut) ref

  val mkFunction        : user -> variable -> hom
  val mkInductive       : user -> hom

  val eval              : hom -> SDD -> SDD
  val evalContext       : hom -> (context * SDD) -> (context * SDD)

  val toString          : hom -> string

  val stats             : unit -> string

  type 'a visitor       =
                     (*Id*)    (unit -> 'a)
                   (*Cons*) -> (variable -> valuation -> hom -> 'a)
                  (*Const*) -> (SDD -> 'a)
                  (*Union*) -> (hom list -> 'a)
           (*Intersection*) -> (hom list -> 'a)
            (*Composition*) -> (hom -> hom -> 'a)
(*Commutative composition*) -> (hom list -> 'a)
               (*Fixpoint*) -> (hom -> 'a)
                 (*Nested*) -> (hom -> variable -> 'a)
               (*Function*) -> (user -> variable -> 'a)
              (*Inductive*) -> (user -> 'a)
                            -> hom
                            -> 'a
  val mkVisitor         : unit -> 'a visitor

  exception NestedHomOnValues
  exception FunctionHomOnNested
  exception EmptyOperands
  exception NotUserHash
  exception NotFuncValues
  exception NotInductiveSkip
  exception NotInductiveValues
  exception NotInductiveOne

end

(*--------------------------------------------------------------------------*)
functor HomFun ( structure SDD : SDD
                 and Variable  : VARIABLE where type t      = SDD.variable
                 and Values    : VALUES   where type values = SDD.values
               )
  : HOM
= struct

(*--------------------------------------------------------------------------*)
exception NestedHomOnValues
exception FunctionHomOnNested
exception EmptyOperands
exception NotUserHash
exception NotFuncValues
exception NotInductiveSkip
exception NotInductiveValues
exception NotInductiveOne

(*--------------------------------------------------------------------------*)
type SDD       = SDD.SDD
type variable  = Variable.t
type values    = Values.values
type valuation = SDD.valuation

(*--------------------------------------------------------------------------*)
type context = (variable * values) list
val emptyContext = []

(*--------------------------------------------------------------------------*)
fun isEmptyContext [] = true
|   isEmptyContext _  = false

(*--------------------------------------------------------------------------*)
fun mergeContexts [] = emptyContext
|   mergeContexts (x::xs) =
let
  fun helper [] x = [x]
  |   helper (L as ((l as (lvr,lvl))::ls)) (x as (xvr,xvl)) =
  if Variable.lt( xvr, lvr ) then
    x::L
  else if Variable.eq( xvr, lvr ) then
    ( xvr, Values.union [lvl,xvl] )::ls
  else
    l::helper ls x
in
  foldl (fn (y,cxt) => foldl (fn (z,cxt') => helper cxt' z) cxt y) x xs
end

(*--------------------------------------------------------------------------*)
fun intersectContexts [] = emptyContext
|   intersectContexts (c::cs) =
let

  fun loop2 res _  [] = res
  |   loop2 res [] _  = res
  |   loop2 res (XS as ((xvr,xvls)::xs)) (YS as ((yvr,yvls)::ys)) =
  if Variable.eq( xvr, yvr ) then
  let
    val vls = Values.intersection [ xvls, yvls ]
  in
    if Values.empty vls then
      loop2 res xs ys
    else
      loop2 ((xvr,vls)::res) xs ys
  end
  else if Variable.lt( xvr, yvr ) then
    loop2 res xs YS
  else
    loop2 res XS ys

  fun loop1 acc [] = acc
  |   loop1 acc (c::cs) =
  let
    val tmp = loop2 [] acc c
  in
    if isEmptyContext tmp then
      emptyContext
    else
      loop1 tmp cs
  end

in
  loop1 c cs
end

(*--------------------------------------------------------------------------*)
fun addValues cxt vr vls =
let
  fun loop [] = [(vr,vls)]
  |   loop (XS as ((x as (xvr,xvls))::xs)) =
  if Variable.eq( vr, xvr ) then
    ( vr, Values.union [xvls,vls] )::xs
  else if Variable.lt( vr, xvr ) then
    ( vr, vls )::XS
  else
    x::loop xs
in
  loop cxt
end

(*--------------------------------------------------------------------------*)
fun removeVariable cxt vr =
  List.filter (fn (xvr,_) => not ( Variable.eq( xvr, vr ) )) cxt

(*--------------------------------------------------------------------------*)
fun eqContext ( [], [] ) = true
|   eqContext ( [], _  ) = false
|   eqContext ( _ , [] ) = false
|   eqContext ( (lvr,lvls)::ls, (rvr,rvls)::rs ) =
  if Variable.eq( lvr, rvr ) andalso Values.eq( lvls, rvls ) then
    eqContext( ls, rs )
  else
    false

(*--------------------------------------------------------------------------*)
structure Definition (* : DATA *) = struct

  structure H = Hash

  datatype hom = Id
               | Cons        of ( variable * valuation * t )
               | Const       of SDD
               | Union       of t list
               | Inter       of t list
               | Comp        of ( t * t )
               | ComComp     of t list
               | Fixpoint    of t
               | Nested      of t * variable
               | Func        of ( (UserIn -> UserOut) ref * variable )
               | Inductive   of (UserIn -> UserOut) ref
               | SatUnion    of ( variable
                                * t option
                                * t list
                                * t option )
               | SatInter    of ( variable
                                * t option    (* F *)
                                * t list      (* G *)
                                * t option )  (* L *)
               | SatFixpoint of ( variable
                                * t option    (* F *)
                                * t list      (* G *)
                                * t option )  (* L *)
               | SatComComp  of ( variable
                                * t           (* F *)
                                * t list      (* G *)
                                )

  and UserIn = FuncValues of (context * values)
             | InductiveSkip of variable
             | InductiveValues of (context * variable * values)
             | InductiveOne
             | Selector
             | Hash
             | Print

  and UserOut = FuncValuesRes of (context * values)
              | InductiveSkipRes of bool
              | InductiveValuesRes of (context * t)
              | InductiveOneRes of SDD
              | SelectorRes of bool
              | HashRes of Hash.t
              | PrintRes of string

  withtype t = (hom * int)


  fun funcString (ref f) =
    (case f Print of
      PrintRes s => s
    | _          => "???"
    )
    handle Match => "???"

  fun funcHash (ref f) =
    case f Hash of
      HashRes h => h
    | _         => raise NotUserHash

 fun eq ( (x,_), (y,_) ) =
 let
   fun eqList ( [], [] ) = true
   |   eqList ( [], _  )  = false
   |   eqList (  _, [] ) = false
   |   eqList ( x::xs, y::ys) =
    if eq( x, y ) then
      eqList( xs, ys )
    else
      false

   fun eqOption ( NONE, NONE ) = true
   |   eqOption ( NONE, _    ) = false
   |   eqOption ( _   , NONE ) = false
   |   eqOption ( SOME x, SOME y ) =
    eq( x, y )

 in
    case (x,y) of
      ( Id, Id )                   => true
    | ( Cons(v,s,h), Cons(w,t,i))  => Variable.eq(v,w)
                                      andalso eq(h,i)
                                      andalso SDD.eqValuation(s,t)
    | ( Const s, Const t )         => SDD.eq( s, t )
    | ( Union xs, Union ys )       => eqList( xs, ys )
    | ( Inter xs, Inter ys )       => eqList( xs, ys )
    | ( Comp(a,b), Comp(c,d) )     => eq( a, c ) andalso eq( b, d )
    | ( ComComp xs, ComComp ys )   => eqList( xs, ys )
    | ( Fixpoint h, Fixpoint i )   => eq( h, i )
    | ( Nested(h,v), Nested(i,w) ) => eq( h, i ) andalso Variable.eq(v,w)
    | ( Func(f,v), Func(g,w) )     => f = g andalso Variable.eq(v,w)
    | ( Inductive i, Inductive j)  => i = j
    | ( SatUnion(v, F, G, L)
      , SatUnion(v',F',G',L'))     => eqOption( F, F' ) andalso eqList( G, G')
                                      andalso eqOption( L, L' )
                                      andalso Variable.eq(v,v')
    | ( SatInter(v, F, G, L)
      , SatInter(v',F',G',L'))     => eqOption( F, F' ) andalso eqList( G, G')
                                      andalso eqOption( L, L' )
                                      andalso Variable.eq(v,v')
    | ( SatFixpoint(v, F, G, L)
      , SatFixpoint(v',F',G',L'))  => eqOption( F, F' ) andalso eqList( G, G')
                                      andalso eqOption( L, L' )
                                      andalso Variable.eq(v,v')
    | ( SatComComp(v, F, G)
      , SatComComp(v',F',G'))      => Variable.eq(v,v') andalso eq( F, F' )
                                      andalso eqList( G, G' )
    | ( _ , _ )                    => false
  end

  fun hash (h,_) =
  let
    fun hashOption NONE                = H.hashInt 183931413
    |   hashOption (SOME (_,uid)) = H.hashInt uid
  in
    case h of
      Id          => H.hashInt 1

    | Cons( v, s, (_,uid) ) =>
      H.hashCombine( Variable.hash v
                   , H.hashCombine( SDD.hashValuation s, H.hashInt uid ) )

    | Const s     => H.hashCombine( SDD.hash s, H.hashInt 149199441 )

    | Union hs    => foldl (fn ( (_,uid),acc) =>
                             H.hashCombine(H.hashInt uid, acc)
                           )
                           (H.hashInt 16564717)
                           hs

    | Inter hs    => foldl (fn ( (_,uid), acc ) =>
                             H.hashCombine(H.hashInt uid, acc)
                           )
                           (H.hashInt 129292632)
                           hs

    | Comp( (_,fuid), (_,guid) ) =>
      H.hashCombine( H.hashInt 3413417
                   , H.hashCombine( H.hashInt fuid, H.hashInt guid )
                   )

    | ComComp hs  => foldl (fn ( (_,uid), acc ) =>
                             H.hashCombine(H.hashInt uid, acc)
                           )
                           (H.hashInt 795921317)
                           hs

    | Fixpoint (_,uid) =>
        H.hashCombine( H.hashInt uid, H.hashInt 5959527)

    | Nested( (_,uid), v ) =>
        H.hashCombine(H.hashInt uid, Variable.hash v )

    | Func(f,v)   => H.hashCombine( H.hashInt 7837892
                                  , H.hashCombine( Variable.hash v
                                                 , funcHash f )
                                  )
    | Inductive i => H.hashCombine( H.hashInt 42429527
                                  , funcHash i
                                  )
    | SatUnion( v, F, G, L) =>
    let
      val hshG = foldl (fn ( (_,uid), acc ) =>
                             H.hashCombine(H.hashInt uid, acc)
                       )
                       (H.hashInt 59489417)
                       G
    in
      H.hashCombine( H.hashInt 48511341
              , H.hashCombine( hashOption F
                 , H.hashCombine( hshG,
                     H.hashCombine(hashOption L, Variable.hash v ))))
    end

    | SatInter( v, F, G, L) =>
    let
      val hshG = foldl (fn ( (_,uid), acc ) =>
                             H.hashCombine(H.hashInt uid, acc)
                       )
                       (H.hashInt 565165613)
                       G
    in
      H.hashCombine( H.hashInt 51454531
              , H.hashCombine( hashOption F
                 , H.hashCombine( hshG,
                     H.hashCombine(hashOption L, Variable.hash v ))))
    end

    | SatFixpoint( v, F, G, L) =>
    let
      val hshG = foldl (fn (  (_,uid), acc ) =>
                             H.hashCombine(H.hashInt uid, acc)
                       )
                       (H.hashInt 19592927)
                       G
    in
      H.hashCombine( H.hashInt 99495913
                , H.hashCombine( hashOption F
                  , H.hashCombine( hshG,
                      H.hashCombine(hashOption L, Variable.hash v ))))
    end

    | SatComComp( v, F, G) =>
    let
      val hshG = foldl (fn ( (_,uid), acc ) =>
                             H.hashCombine(H.hashInt uid, acc)
                       )
                       (H.hashInt 87284791)
                       G
    in
      H.hashCombine( H.hashInt 30918931
                , H.hashCombine( hash F
                  , H.hashCombine( hshG, Variable.hash v )))
    end

  end

  fun toString (h,_) =
  let
    fun optPartToString NONE      = ""
    |   optPartToString (SOME x) = toString x
  in
  case h of
      Id          => "Id"
    | Cons(v,s,h) => "Cons(" ^ (Variable.toString v)
                             ^ ", "
                             ^ (SDD.valuationToString s)
                             ^ ", "
                             ^ (toString h)
                             ^ ")"
    | Const s     => "Const(" ^ (SDD.toString s) ^ ")"
    | Union hs    => String.concatWith " + " (map toString hs)
    | Inter hs    => String.concatWith " ^ "
                                       (map toString hs)
    | Comp(a,b)   => (toString a) ^ " o " ^ (toString b)
    | ComComp hs  => String.concatWith " @ "
                                       (map toString hs)
    | Fixpoint h  => "(" ^ (toString h) ^ ")*"
    | Nested(h,v) => "Nested(" ^ (toString h) ^", "
                               ^ (Variable.toString v) ^ ")"
    | Func(f,v)   => "Func(" ^ (funcString f) ^ ","
                      ^ (Variable.toString v) ^ ")"
    | Inductive i => "Inductive(" ^ (funcString i) ^ ")"
    | SatUnion(_, F, G, L) =>    "F(" ^ (optPartToString F) ^ ") + "
                                ^ "G("
                                ^ (String.concatWith " + " (map toString G))
                                ^ ") + "
                                ^	"L(" ^ (optPartToString L) ^ ")"

    | SatInter(_, F, G, L) =>    "F(" ^ (optPartToString F) ^ ") ^ "
                                ^ "G("
                                ^ (String.concatWith " ^ " (map toString G))
                                ^ ") ^ "
                                ^	"L(" ^ (optPartToString L) ^ ")"

    | SatFixpoint(_, F, G, L) =>  "("
                                ^ "F(" ^ (optPartToString F) ^ ") + "
                                ^ "G("
                                ^ (String.concatWith " + " (map toString G))
                                ^ ") + "
                                ^	"L(" ^ (optPartToString L) ^ ") )*"

    | SatComComp(_, F, G) =>      "F(" ^ (toString F) ^ ") @ "
                                ^ "G("
                                ^ (String.concatWith " @ " (map toString G))
                                ^ ")"
  end

  fun configure UnicityTableConfiguration.Name =
    UnicityTableConfiguration.NameRes "Hom"
  |   configure UnicityTableConfiguration.Buckets =
    UnicityTableConfiguration.BucketsRes 10000

end (* structure Definition *)
open Definition

(*--------------------------------------------------------------------------*)
type hom     = Definition.t

structure UT = UnicityTableFunID( structure Data = Definition )
structure HT = HashTable

(*--------------------------------------------------------------------------*)
type user = (UserIn -> UserOut) ref

(*--------------------------------------------------------------------------*)
fun funcValues (ref f) param =
  case f (FuncValues param) of
    FuncValuesRes res => res
  | _                 => raise NotFuncValues

(*--------------------------------------------------------------------------*)
fun inductiveValues (ref i) param =
  case i (InductiveValues param) of
    InductiveValuesRes res => res
  | _                      => raise NotInductiveValues

(*--------------------------------------------------------------------------*)
fun inductiveOne (ref i) =
  case i InductiveOne of
    InductiveOneRes s => s
  | _                 => raise NotInductiveOne

(*--------------------------------------------------------------------------*)
fun inductiveSkip (ref i) var =
  case i (InductiveSkip var ) of
    InductiveSkipRes b => b
  | _                  => raise NotInductiveSkip

(*--------------------------------------------------------------------------*)
fun funcSelector (ref f) =
  (case f Selector of
    SelectorRes b => b
  | _             => false
  )
  handle Match => false

(*--------------------------------------------------------------------------*)
(* Called by the unicity table to construct an homomorphism with an id *)
fun mkHom hom uid = ( hom, uid )

(*--------------------------------------------------------------------------*)
fun uid (_,x) = x

(*--------------------------------------------------------------------------*)
fun eq (h1,h2) = uid h1 = uid h2

(*--------------------------------------------------------------------------*)
val id = UT.unify( mkHom Id )

(*--------------------------------------------------------------------------*)
datatype domain = All
                | Empty
                | Variables of (variable list)

(*--------------------------------------------------------------------------*)
fun emptyDomainIntersection x y =
  case ( x, y ) of
    ( All, _ )   => false
  | ( _, All )   => false
  | ( Empty, _ ) => true
  | ( _, Empty ) => true
  | ( Variables ls, Variables rs ) =>
    let

      fun helper ls rs =
        case ( ls, rs ) of
          ( _, [] ) => true
        | ( [], _ ) => true
        | ( l::ls, r::rs ) =>
          if Variable.eq( l, r ) then
            false
          else
            helper ls rs

    in
      helper ls rs
    end

(*--------------------------------------------------------------------------*)
fun domainUnion []         = Empty
|   domainUnion [x]        = x
|   domainUnion (x::y::xs) =
  case ( x, y ) of
    ( All, _ )   => All
  | ( _, All )   => All
  | ( Empty, _ ) => y
  | ( _, Empty ) => x
  | ( Variables ls, Variables rs ) =>
  let

    fun insert [] x = [x]
    |   insert (L as (l::ls)) x =
      if Variable.eq( x, l ) then
        L
      else if Variable.lt( x, l ) then
        x::L
      else
        l::insert ls x

    fun merge xs [] = xs
    |   merge xs (y::ys) =
      merge (insert xs y) ys

  in
    domainUnion ((Variables (merge ls rs))::xs)
  end

(*--------------------------------------------------------------------------*)
fun domain (h,_) =
  case h of
    Nested( _, v )  => Variables [v]
  | Func( _, v )    => Variables [v]
  | Comp( a, b )    => domainUnion [ domain a, domain b ]
  | ComComp xs      => domainUnion (foldr (fn (h,l) => (domain h)::l) [] xs)
  | Union xs        => domainUnion (foldr (fn (h,l) => (domain h)::l) [] xs)
  | Inter xs        => domainUnion (foldr (fn (h,l) => (domain h)::l) [] xs)

  | SatUnion(v,F,G,L) =>
  let
    val dF = case F of
               NONE   => Empty
             | SOME f => domain f
    val dG = domainUnion (foldr (fn (h,l) => (domain h)::l) [] G)
    val dL = case L of
               NONE   => Empty
             | SOME l => domain l
  in
    domainUnion [ Variables [v], dF, dG, dL ]
  end

  | SatInter(v,F,G,L) =>
  let
    val dF = case F of
               NONE   => Empty
             | SOME f => domain f
    val dG = domainUnion (foldr (fn (h,l) => (domain h)::l) [] G)
    val dL = case L of
               NONE   => Empty
             | SOME l => domain l
  in
    domainUnion [ Variables [v], dF, dG, dL ]
  end

  | SatFixpoint(v,F,G,L) =>
  let
    val dF = case F of
               NONE   => Empty
             | SOME f => domain f
    val dG = domainUnion (foldr (fn (h,l) => (domain h)::l) [] G)
    val dL = case L of
               NONE   => Empty
             | SOME l => domain l
  in
    domainUnion [ Variables [v], dF, dG, dL ]
  end

  | SatComComp(v,F,G) =>
  let
    val dF = domain F
    val dG = domainUnion (foldr (fn (h,l) => (domain h)::l) [] G)
  in
    domainUnion [ Variables [v], dF, dG ]
  end

  | _               => All

(*--------------------------------------------------------------------------*)
fun isSelector (h,_) =
let
  fun selectorOption NONE     = true
  |   selectorOption (SOME h) = isSelector h
in
  case h of
    Func(f,_)            => funcSelector f
  | Nested(g,_)          => isSelector g
  | Union hs             => List.all isSelector hs
  | Inter hs             => List.all isSelector hs
  | Comp(f,g)            => isSelector f andalso isSelector g
  | ComComp hs           => List.all isSelector hs
  | Fixpoint g           => isSelector g
  | SatUnion(_,F,G,L)    => selectorOption F
                            andalso List.all isSelector G
                            andalso selectorOption L
  | SatInter(_,F,G,L)    => selectorOption F
                            andalso List.all isSelector G
                            andalso selectorOption L
  | SatFixpoint(_,F,G,L) => selectorOption F
                            andalso List.all isSelector G
                            andalso selectorOption L
  | SatComComp(_,F,G)    => isSelector F andalso List.all isSelector G
  | _                    => false
end

(*--------------------------------------------------------------------------*)
fun commutatives x y =
  if isSelector(x) andalso isSelector(y) then
    true
  else if emptyDomainIntersection (domain x) (domain y) then
    true
  else
    case ( #1 x, #1 y ) of
      ( Nested( g1, v1 ), Nested( g2, v2) ) =>
        Variable.eq(v1,v2) andalso commutatives g1 g2
    | ( _, _ ) => false

(*--------------------------------------------------------------------------*)
fun mkCons var vl next =
  UT.unify( mkHom (Cons(var,vl,next)) )

(*--------------------------------------------------------------------------*)
fun mkConst sdd =
  UT.unify( mkHom (Const(sdd)) )

(*--------------------------------------------------------------------------*)
val zero = mkConst SDD.zero
val one  = mkConst SDD.one

(*--------------------------------------------------------------------------*)
fun mkNested h vr =
  if eq( h, id ) then
    id
  else
    UT.unify( mkHom (Nested(h,vr)) )

(*--------------------------------------------------------------------------*)
fun mkCommutativeComposition [] = raise EmptyOperands
|   mkCommutativeComposition hs =
let

  fun helper ( h, operands ) =
    case #1 h of
      Id              => operands
    | ComComp ys      => (foldr helper [] ys) @ operands
    | _               => h::operands

  val operands0 = foldr helper [] hs
  val (sel,NotSel) = List.partition isSelector operands0
  val operands = sel @ NotSel

in
  case operands of
    []  => raise EmptyOperands
  | [x] => x
  | _   => let
             val operands' = Util.sort uid (op<) operands
           in
             UT.unify( mkHom (ComComp operands') )
           end
end

(*--------------------------------------------------------------------------*)
fun mkUnion' []  = raise EmptyOperands
|   mkUnion' [x] = x
|   mkUnion' xs  =
let

  val nesteds : ( ( variable , hom list ref ) HT.hash_table )
      = (HT.mkTable( Variable.hash , Variable.eq ) ( 10000, DoNotPanic ))

  fun unionHelper ( h, operands ) =
  case #1 h of

    Union ys      => foldr unionHelper operands ys

  | Nested(g,v)   => (case HT.find nesteds v of
                       NONE    => HT.insert nesteds ( v, ref [g] )
                     | SOME hs => hs := !hs @ [g]
                     ; operands
                     )

  | _             => h::operands

  val operands = foldr unionHelper [] xs

  val nesteds' = HT.foldi (fn ( v, ref hs, acc) =>
                            (mkNested (mkUnion' hs) v) :: acc
                          )
                          []
                          nesteds

  val operands' = nesteds' @ operands

in
  case operands' of
    []  => raise EmptyOperands
  | [x] => x
  | _   => UT.unify( mkHom (Union operands') )
end

(*--------------------------------------------------------------------------*)
(* A sorting wrapper for mkUnion' which does the real job.
   Prefer mkUnion' for internal work. *)
val mkUnion = mkUnion' o (Util.sortUnique uid (op<) (op>))

(*--------------------------------------------------------------------------*)
fun mkIntersection []  = raise EmptyOperands
|   mkIntersection [x] = x
|   mkIntersection xs  =
  UT.unify( mkHom (Inter xs) )

(*--------------------------------------------------------------------------*)
fun mkComposition x y =
  if eq( y, id ) then
    x
  else if eq( x, id ) then
    y
  else
  let

    fun addParameter xs y =
    case #1 y of

      ComComp ys  => foldl (fn (x,acc) => addParameter acc x) xs ys

    | Nested(f,v) =>
    let
      fun loop [] = [y]
      |   loop ((rx as (x,_))::xs) =
       case x of
         Nested(g,w) => if Variable.eq( v, w ) then
                          (mkNested (mkComposition g f) v)::xs
                        else
                          rx::loop xs
       | _ => rx::loop xs
    in
      loop xs
    end

    | _ =>
    let
      val (c,notC) = List.partition (fn x => commutatives x y) xs
      fun mkComp x y = UT.unify( mkHom (Comp( x, y )) )
    in
      case notC of
        []  => y::c
      | [x] => (mkComp x y)::c
      | _   => (mkComp (mkCommutativeComposition notC) y)::c
    end

  in
    case addParameter (addParameter [] x) y of
      [x] => x
    | xs  => mkCommutativeComposition xs
  end

(*--------------------------------------------------------------------------*)
fun mkFixpoint h =
  case #1 h of
    Id          => h
  | Fixpoint _  => h
  | _           => UT.unify( mkHom (Fixpoint h) )

(*--------------------------------------------------------------------------*)
fun mkFunction f var =
  UT.unify( mkHom (Func(f,var)) )

(*--------------------------------------------------------------------------*)
fun mkInductive i =
  UT.unify( mkHom (Inductive i) )

(*--------------------------------------------------------------------------*)
fun mkSatUnion var F G L =
  UT.unify( mkHom (SatUnion(var, F, G, L)) )

(*--------------------------------------------------------------------------*)
fun mkSatIntersection var F G L =
  UT.unify( mkHom (SatInter(var, F, G, L)) )

(*--------------------------------------------------------------------------*)
fun mkSatFixpoint var F G L =
  UT.unify( mkHom (SatFixpoint(var, F, G, L)) )

(*--------------------------------------------------------------------------*)
fun mkSatComComp var F G =
let
  val G' = Util.sort uid (op<) G
in
  UT.unify( mkHom (SatComComp(var, F, G' )) )
end

(*--------------------------------------------------------------------------*)
structure Evaluation (* : OPERATION *) = struct

(*--------------------------------------------------------------------------*)
fun configure CacheConfiguration.Name =
  CacheConfiguration.NameRes "Hom"

(*--------------------------------------------------------------------------*)
type result        = ( context * SDD )
datatype operation = Op of hom * context * SDD * (operation -> result)

(*--------------------------------------------------------------------------*)
val eq' = eq
fun eq ( Op(xh,_,xsdd,_), Op(yh,_,ysdd,_) ) =
  eq'( xh, yh ) andalso SDD.eq( xsdd, ysdd )

(*--------------------------------------------------------------------------*)
fun hash ( Op( (_,uid), _, sdd, _ ) ) =
  H.hashCombine( H.hashInt uid, SDD.hash sdd )

(*--------------------------------------------------------------------------*)
fun skipVariable var h =
  case #1 h of
    Id                   => true
  | Const _              => false
  | Cons(_,_,_)          => false
  | Nested(_,v)          => not (Variable.eq (var,v))
  | Union hs             => List.all (skipVariable var) hs
  | Inter hs             => List.all (skipVariable var) hs
  | Comp(a,b)            => skipVariable var a andalso skipVariable var b
  | ComComp hs           => List.all (skipVariable var) hs
  | Fixpoint f           => skipVariable var f
  | Func(_,v)            => not (Variable.eq (var,v))
  | Inductive i          => inductiveSkip i var
  | SatUnion(v,_,_,_)    => not (Variable.eq (var,v))
  | SatInter(v,_,_,_)    => not (Variable.eq (var,v))
  | SatFixpoint(v,_,_,_) => not (Variable.eq (var,v))
  | SatComComp(v,_,_)    => not (Variable.eq (var,v))

(*--------------------------------------------------------------------------*)
(* Evaluate an homomorphism on an SDD. Warning! Duplicate with Hom.eval! *)
fun evalCallback lookup h (cxt,sdd) =
  if SDD.empty sdd then
    ( emptyContext, SDD.zero )
  else
    case #1 h of
      Id                => ( cxt, sdd )
    | Const c           => ( cxt, c )
    | Cons(var,vl,next) => if eq'( next, id ) then
                                      ( cxt, SDD.node( var, vl, sdd ) )
                                    else
                                      lookup( Op( h, cxt, sdd, lookup ) )
    | _                 => lookup( Op( h, cxt, sdd, lookup ) )

(*--------------------------------------------------------------------------*)
val rewritten = ref 0
val eligible  = ref 0
val processed = ref 0

(*--------------------------------------------------------------------------*)
structure Rewrite (* : OPERATION *) = struct

(*--------------------------------------------------------------------------*)
fun configure CacheConfiguration.Name =
  CacheConfiguration.NameRes "Rewrite"
|   configure CacheConfiguration.Buckets =
  CacheConfiguration.BucketsRes 100000

(*--------------------------------------------------------------------------*)
type operation = ( hom * variable )
type result    = hom

(*--------------------------------------------------------------------------*)
fun eq ((hx,vx),(hy,vy)) = eq'(hx,hy) andalso Variable.eq(vx,vy)

(*--------------------------------------------------------------------------*)
fun hash ( (_,uid), v ) =
  H.hashCombine( H.hashInt uid, Variable.hash v )

(*--------------------------------------------------------------------------*)
fun partition v hs =
let

  fun helper ( h, (F,G,L) ) =
    if skipVariable v h then
      ( h::F, G, L )
    else
      case let val (x,_) = h in x end of
        Nested(n,_) => ( F, G, n::L )
      | _           => ( F, h::G, L )

  val (F,G,L) = foldr helper ([],[],[]) hs
  val F' = if length F = 0 then NONE else SOME F
  val L' = if length L = 0 then NONE else SOME L

in
  ( F', G, L' )
end

(*--------------------------------------------------------------------------*)
fun rewriteUI operation mk orig v xs =
let
  val (F,G,L) = partition v xs
in

  if not (Option.isSome F) andalso not (Option.isSome L) then
    orig

  else
  let
    val F' = case F of
               NONE   => NONE
             | SOME f => SOME (operation f)
    val L' = case L of
               NONE   => NONE
             | SOME l => SOME (mkNested (operation l) v)
    val _ = rewritten := !rewritten + 1
  in
    mk v F' G L'
  end

end

(*--------------------------------------------------------------------------*)
fun rewriteFixpoint orig v f =

  case let val (h,_) = f in h end of

    Union xs =>
      if List.exists (fn x => eq'(x,id)) xs then
      let
        val (F,G,L) = partition v xs
        val (GSel,GNotSel) = List.partition isSelector G
      in
        if not (Option.isSome F) andalso not (Option.isSome L) then
          orig

        else
        let
          val F' =
            case F of
              NONE   => NONE
            | SOME f => SOME (mkFixpoint(mkUnion' f)) (* id is contained *)
          val L' =
            case L of
              NONE   => NONE
            | SOME l => SOME (mkNested (mkFixpoint (mkUnion' (id::l))) v)
          val _ = rewritten := !rewritten + 1;
        in
          mkSatFixpoint v F' (GSel@GNotSel) L'
        end
      end

      else (* No id in operands*)
        orig

  | _ => orig

(*--------------------------------------------------------------------------*)
fun rewriteComComp orig v hs =
let
  val (F,G) = List.partition (skipVariable v) hs
in
  case F of
    [] => orig
  | fs =>
  let
    val (GSel,GNotSel) = List.partition isSelector G
  in
    mkSatComComp v (mkCommutativeComposition fs) (GSel@GNotSel)
  end
end

(*--------------------------------------------------------------------------*)
fun apply ( h, v ) =
  case #1 h of
    Union hs    => rewriteUI mkUnion' mkSatUnion h v hs
  | Inter hs    => rewriteUI mkIntersection mkSatIntersection h v hs
  | Fixpoint f  => rewriteFixpoint h v f
  | ComComp hs  => rewriteComComp h v hs
  | _           => raise DoNotPanic

end (* structure Rewrite *)

(*--------------------------------------------------------------------------*)
structure rewriteCache = CacheFun(structure Operation = Rewrite)

(*--------------------------------------------------------------------------*)
fun rewrite h v =
let
  val _ = processed := !processed + 1
in
  case #1 h of
    Union _    => (eligible := !eligible + 1; rewriteCache.lookup (h,v))
  | Inter _    => (eligible := !eligible + 1; rewriteCache.lookup (h,v))
  | Fixpoint _ => (eligible := !eligible + 1; rewriteCache.lookup (h,v))
  | ComComp _  => (eligible := !eligible + 1; rewriteCache.lookup (h,v))
  | _          => h
end

(*--------------------------------------------------------------------------*)
(* Evaluate a list of homomorphisms and insert the result sorted into a list
   of results *)
fun evalInsertMerge eval hs xs (cxt,sdd) =
let
  (* sort results using the right hand member (sdd) *)
  fun helper [] x = [x]
  |   helper (L as ((l as (lcxt,lsdd))::ls)) (x as (xcxt,xsdd)) =
    if SDD.eq( xsdd, lsdd ) then
      ( mergeContexts [lcxt,xcxt], lsdd)::ls
    else if SDD.lt( xsdd, lsdd ) then
      x::L
    else
      l::helper ls x
in
  foldl (fn (h,acc) => helper acc (eval h (cxt,sdd)) ) xs hs
end

(*--------------------------------------------------------------------------*)
fun cons eval (var, vl, hsucc) x =
let
  val ( cxt', succ' ) = eval hsucc x
in
  ( cxt', SDD.node( var, vl, succ') )
end

(*--------------------------------------------------------------------------*)
fun union eval hs x =
let
  val (cxts,sdds) = ListPair.unzip( evalInsertMerge eval hs [] x )
in
  ( mergeContexts cxts, SDD.union sdds )
end

(*--------------------------------------------------------------------------*)

fun intersection eval hs x =
let
  fun loop res [] = res
  |   loop res (h::hs) =
  let
    val tmp as (cxt,sdd) = eval h x
  in
    if SDD.eq( sdd, SDD.zero ) then
      [(emptyContext,SDD.zero)]
    else
    let
      (* Insert sort using right hand member (sdd) *)
      fun helper [] x = [x]
      |   helper (L as ((l as (lcxt,lsdd))::ls)) (x as (xcxt,xsdd)) =
        if SDD.eq( xsdd, lsdd ) then
          ( mergeContexts [lcxt,xcxt], lsdd)::ls
        else if SDD.lt( xsdd, lsdd ) then
          x::L
        else
          l::helper ls x
    in
      loop (helper res tmp) hs
    end
  end

  val (cxts,sdds) = ListPair.unzip( loop [] hs )
in
  ( intersectContexts cxts, SDD.intersection sdds )
end

(*--------------------------------------------------------------------------*)
fun satUnion eval F G L (x as (cxt,sdd)) =
let
  val fres = case F of NONE => [] | SOME f => [eval f x]
  val gres = evalInsertMerge eval G fres x
  val lres = case L of NONE   => gres
                     | SOME l => evalInsertMerge eval [l] gres x
  val (cxts,sdds) = ListPair.unzip lres
in
  ( mergeContexts cxts, SDD.union sdds )
end

(*--------------------------------------------------------------------------*)
fun satIntersection eval F G L (x as (cxt,sdd)) =
let
  fun run f = eval f x
  fun runG () = intersection eval G x
in

  case ( F, L ) of
    ( NONE, NONE )     => runG ()

  | ( SOME f, NONE)    =>
  let
    val fRes as ( fcxt, fsdd ) = run f
  in
    if SDD.eq( fsdd, SDD.zero ) then
      ( emptyContext, SDD.zero )
    else
    let
      val ( gcxt, gsdd ) = runG ()
    in
      if SDD.eq( gsdd, SDD.zero ) then
        ( emptyContext, SDD.zero )
      else
        ( intersectContexts [fcxt,gcxt], SDD.intersection [fsdd,gsdd])
    end
  end

  | ( NONE, SOME l )   =>
  let
    val lRes as ( lcxt, lsdd ) = run l
  in
    if SDD.eq( lsdd, SDD.zero ) then
      ( emptyContext, SDD.zero )
    else
    let
      val ( gcxt, gsdd ) = runG ()
    in
      if SDD.eq( gsdd, SDD.zero ) then
        ( emptyContext, SDD.zero )
      else
        ( intersectContexts [lcxt,gcxt], SDD.intersection [lsdd,gsdd])
    end
  end

  | ( SOME f, SOME l ) =>
  let
    val fRes as ( fcxt, fsdd ) = run f
  in
    if SDD.eq( fsdd, SDD.zero ) then
      ( emptyContext, SDD.zero )
    else
    let
      val lRes as ( lcxt, lsdd ) = run l
    in
      if SDD.eq( lsdd, SDD.zero ) then
        ( emptyContext, SDD.zero )
      else
      let
        val ( gcxt, gsdd ) = runG ()
      in
        if SDD.eq( gsdd, SDD.zero ) then
          ( emptyContext, SDD.zero )
        else
          ( intersectContexts [ fcxt, lcxt, gcxt ]
          , SDD.intersection  [ fsdd, lsdd, gsdd]
          )
      end
    end
  end
end

(*--------------------------------------------------------------------------*)
fun composition eval a b x =
  eval a (eval b x)

(*--------------------------------------------------------------------------*)
fun commutativeComposition eval hs x =
  foldl (fn (h,y) => eval h y) x hs

(*--------------------------------------------------------------------------*)
fun satCommutativeComposition eval F G x =
  foldl (fn (g,y) => eval g y) (eval F x) G

(*--------------------------------------------------------------------------*)
fun fixpoint eval h (x as (cxt,sdd)) =
let
  val res as (cxt',sdd') = eval h x
in
  if SDD.eq( sdd', sdd ) then
    res
  else
    fixpoint eval h (cxt',sdd')
end

(*--------------------------------------------------------------------------*)
fun satFixpoint eval F G L (x as (cxt,sdd)) =
let
  val fres as ( fcxt, fsdd ) = case F of NONE => x
                                       | SOME f => eval f x
  val lres                   = case L of NONE => fres
                                       | SOME l => eval l (fcxt,fsdd)
  val gres as ( gcxt, gsdd ) = foldl (fn ( g, (cxt,sdd) ) =>
                                     let
                                       val (cxt',sdd') = eval g (cxt,sdd)
                                     in
                                       ( cxt', SDD.union[ sdd, sdd'] )
                                     end
                                     )
                                     lres
                                     G
in
  if SDD.eq( gsdd, sdd ) then
    gres
  else
    satFixpoint eval F G L (gcxt,gsdd)
end

(*--------------------------------------------------------------------------*)
fun nested eval h var (cxt,sdd) =
  if SDD.eq( sdd, SDD.one ) then
    ( cxt, SDD.one )
  else
  let
    val tmp = map (fn ( vl, succ) =>
                    case vl of
                      SDD.Values _   => raise NestedHomOnValues
                    | SDD.Nested nvl =>
                    let
                      val (cxt',nvl') = eval h (cxt,nvl)
                    in
                      ( cxt', ( SDD.Nested nvl', succ ) )
                    end
                  )
                  (SDD.alpha sdd)
    val (cxts,arcs) = ListPair.unzip tmp
    val cxt' = mergeContexts cxts
  in
    if isSelector h then
      ( cxt'
      , SDD.nodeAlpha( var, arcs )
      )
    else
      ( cxt'
      , SDD.union (foldl (fn ((vl,succ),acc) =>
                    SDD.insert acc( SDD.node( var, vl, succ ) )
                  )
                  []
                  arcs
                  )
      )
  end

(*--------------------------------------------------------------------------*)
fun function f var (cxt,sdd) =
  if SDD.eq( sdd, SDD.one ) then
    ( cxt, SDD.one )
  else
  let
    val tmp = map (fn ( vl, succ) =>
                    case vl of
                      SDD.Nested _      => raise FunctionHomOnNested
                    | SDD.Values values =>
                    let
                      val (cxt',values') = funcValues f (cxt,values)
                    in
                      ( cxt', ( SDD.Values values', succ ) )
                    end
                  )
                  (SDD.alpha sdd)
    val (cxts,arcs) = ListPair.unzip tmp
    val cxt' = mergeContexts cxts
  in
    if funcSelector f then
      ( cxt'
      , SDD.nodeAlpha( var, arcs )
      )
    else
      ( cxt'
      , SDD.union (foldl (fn ((vl,succ),acc) =>
                    SDD.insert acc( SDD.node( var, vl, succ ) )
                  )
                  []
                  arcs
                  )
      )
  end

(*--------------------------------------------------------------------------*)
fun inductive eval i (cxt,sdd) =
  if SDD.eq( sdd, SDD.one ) then
    ( cxt, inductiveOne i )
  else
  let
    val var = SDD.variable sdd
    val tmp = map (fn ( vl, succ) =>
                    case vl of
                      SDD.Nested _      => raise Domain
                    | SDD.Values values =>
                    let
                      val (cxt',h) = inductiveValues i (cxt,var,values)
                    in
                      eval h (cxt',succ)
                    end
                  )
                  (SDD.alpha sdd)
    val (cxts,sdds) = ListPair.unzip tmp
  in
    ( mergeContexts cxts, SDD.union (SDD.sort sdds) )
  end

(*--------------------------------------------------------------------------*)
val evals   = ref 0
val skipped = ref 0

(* Dispatch the evaluation of an homomorphism to the corresponding
   function. Used by CacheFun.
*)
fun apply ( Op( h, cxt, sdd, lookup ) ) =
let
  val _ = evals := !evals + 1
  val skip = let val v = SDD.variable sdd in skipVariable v h end
             handle SDD.IsNotANode => false
  val eval = evalCallback lookup
in
  if skip then
    let
      val _ = skipped := !skipped + 1
      val var = SDD.variable sdd
      val tmp = map (fn ( vl, succ) =>
                    let
                      val (cxt',succ') = eval h (cxt,succ)
                    in
                      ( cxt', (vl,succ') )
                    end
                    )
                    (SDD.alpha sdd)
      val (cxts,arcs) = ListPair.unzip tmp
      val cxt' = mergeContexts cxts
    in
      if isSelector h then
        ( cxt'
        , SDD.nodeAlpha( var, arcs )
        )
      else
        ( cxt'
        , SDD.union( SDD.sort( map (fn (vl,succ) => SDD.node( var, vl, succ))
                                   arcs
                             )
                   )
        )
    end
  else
  let
    (* All saturation enabled operations can only be created by the rewritting
       process. Thus, when sdd is a terminal, h' can never be a saturation
       operation.
    *)
    val h' = rewrite h (SDD.variable sdd)
             handle SDD.IsNotANode => h
  in
    case #1 h' of
      Id                    => raise DoNotPanic
    | Const _               => raise DoNotPanic
    | Cons(var,nested,next) => cons eval (var, nested, next) (cxt,sdd)
    | Union hs              => union eval hs (cxt,sdd)
    | Inter hs              => intersection eval hs (cxt,sdd)
    | Comp( a, b )          => composition eval a b (cxt,sdd)
    | ComComp hs            => commutativeComposition eval hs (cxt,sdd)
    | Fixpoint g            => fixpoint eval g (cxt,sdd)
    | Nested( g, var )      => nested eval g var (cxt,sdd)
    | Func( f, var )        => function f var (cxt,sdd)
    | Inductive i           => inductive eval i (cxt,sdd)
    | SatUnion( _, F, G, L) => satUnion eval F G L (cxt,sdd)
    | SatInter( _, F, G, L) => satIntersection eval F G L (cxt,sdd)
    | SatFixpoint(_,F,G,L)  => satFixpoint eval F G L (cxt,sdd)
    | SatComComp(_,F,G)     => satCommutativeComposition eval F G (cxt,sdd)
  end

end (* fun apply *)

(*--------------------------------------------------------------------------*)
end (* structure Evaluation *)

(*--------------------------------------------------------------------------*)
structure cache = CacheFun(structure Operation = Evaluation)
val cacheLookup = cache.lookup

(* Evaluate an homomorphism on an SDD.
   Warning! Duplicate logic with Evaluation.evalCallback!
*)
fun evalContext h (x as (cxt,sdd)) =
  if SDD.eq( sdd, SDD.zero ) then
    ( emptyContext, SDD.zero )
  else
    case #1 h of
      Id                => x
    | Const c           => ( cxt, c )
    | Cons(var,vl,next) =>
      if eq( next, id ) then
        ( cxt, SDD.node( var, vl, sdd ) )
      else
        cache.lookup( Evaluation.Op( h, cxt, sdd, cacheLookup ) )
    | _ => cache.lookup( Evaluation.Op( h, cxt, sdd, cacheLookup ) )

(*--------------------------------------------------------------------------*)
(* Evaluate an homomorphism on an SDD, ignoring the evaluation context *)
fun eval h sdd = #2( evalContext h (emptyContext,sdd) )

(*--------------------------------------------------------------------------*)
type 'a visitor =
                     (*Id*)    (unit -> 'a)
                   (*Cons*) -> (variable -> valuation -> hom -> 'a)
                  (*Const*) -> (SDD -> 'a)
                  (*Union*) -> (hom list -> 'a)
           (*Intersection*) -> (hom list -> 'a)
            (*Composition*) -> (hom -> hom -> 'a)
(*Commutative composition*) -> (hom list -> 'a)
               (*Fixpoint*) -> (hom -> 'a)
                 (*Nested*) -> (hom -> variable -> 'a)
               (*Function*) -> (user -> variable -> 'a)
              (*Inductive*) -> (user -> 'a)
                            -> hom
                            -> 'a

(*--------------------------------------------------------------------------*)
fun mkVisitor (():unit) : 'a visitor =
let

  fun visitor id cons const union inter comp comcomp fixpoint nested func
              inductive h
  =
    case #1 h of
      Id              => id ()
    | Cons(v,vl,nxt)  => cons v vl nxt
    | Const s         => const s
    | Union hs        => union hs
    | Inter hs        => inter hs
    | Comp(a,b)       => comp a b
    | ComComp hs      => comcomp hs
    | Fixpoint h      => fixpoint h
    | Nested(h,v)     => nested h v
    | Func(f,v)       => func f v
    | Inductive i     => inductive i
    | _               => raise DoNotPanic

in
  visitor
end

(*--------------------------------------------------------------------------*)
fun stats () = (cache.stats()) ^ (Evaluation.rewriteCache.stats())
               ^ "\n-----------------\n"
               ^ "Homomorphisms\n"
               ^ "processed: " ^ (Int.toString (!Evaluation.processed))
               ^ " | eligible: " ^ (Int.toString (!Evaluation.eligible))
               ^ " | rewritten: " ^ (Int.toString (!Evaluation.rewritten))
               ^ "\n"
               ^ "evals: " ^ (Int.toString (!Evaluation.evals))
               ^ " | skipped: " ^ (Int.toString (!Evaluation.skipped))
               ^ "\n"

(*--------------------------------------------------------------------------*)
end (* functor HomFun *)
