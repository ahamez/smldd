(*--------------------------------------------------------------------------*)
signature HOM = sig

  type hom
  type SDD
  type variable
  type values
  type valuation

  val eq              : hom * hom -> bool
  val uid             : hom -> int

  val id              : hom
  val zero            : hom
  val one             : hom
  val mkCons          : variable -> valuation -> hom -> hom
  val mkConst         : SDD -> hom
  val mkUnion         : hom list -> hom
  val mkIntersection  : hom list -> hom
  val mkComposition   : hom -> hom -> hom
  val mkFixpoint      : hom -> hom
  val mkNested        : hom -> variable -> hom

  datatype UserIn     = FuncValues of values
                      | InductiveSkip of variable
                      | InductiveValues of (variable * values)
                      | InductiveOne
                      | Selector
                      | Hash
                      | Print

  datatype UserOut    = FuncValuesRes of values
                      | InductiveSkipRes of bool
                      | InductiveValuesRes of hom
                      | InductiveOneRes of SDD
                      | SelectorRes of bool
                      | HashRes of Hash.t
                      | PrintRes of string

  type user           = (UserIn -> UserOut) ref

  val mkFunction      : user -> variable -> hom
  val mkInductive     : user -> hom

  val eval            : hom -> SDD -> SDD

  val toString        : hom -> string

  val stats           : unit -> string

  type 'a visitor     =
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
  val mkVisitor       : unit -> 'a visitor

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
structure Definition (* : DATA *) = struct

  structure H = Hash

  datatype t = Hom of ( hom * int )
  and hom    = Id
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
                              * t             (* F *)
                              * t list        (* G *)
                              )

  and UserIn = FuncValues of values
             | InductiveSkip of variable
             | InductiveValues of (variable * values)
             | InductiveOne
             | Selector
             | Hash
             | Print

  and UserOut = FuncValuesRes of values
              | InductiveSkipRes of bool
              | InductiveValuesRes of t
              | InductiveOneRes of SDD
              | SelectorRes of bool
              | HashRes of Hash.t
              | PrintRes of string

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

 fun eq (Hom(x,_),Hom(y,_)) =
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

  fun hash (Hom(h,_)) =
  let
    fun hashOption NONE                = H.hashInt 183931413
    |   hashOption (SOME (Hom(_,uid))) = H.hashInt uid
  in
    case h of
      Id          => H.hashInt 1

    | Cons( v, s, Hom(_,uid) ) =>
      H.hashCombine( Variable.hash v
                   , H.hashCombine( SDD.hashValuation s, H.hashInt uid ) )

    | Const s     => H.hashCombine( SDD.hash s, H.hashInt 149199441 )

    | Union hs    => foldl (fn (Hom(_,uid),acc) =>
                             H.hashCombine(H.hashInt uid, acc)
                           )
                           (H.hashInt 16564717)
                           hs

    | Inter hs    => foldl (fn ( Hom(_,uid), acc ) =>
                             H.hashCombine(H.hashInt uid, acc)
                           )
                           (H.hashInt 129292632)
                           hs

    | Comp( Hom(_,fuid), Hom(_,guid) ) =>
      H.hashCombine( H.hashInt 3413417
                   , H.hashCombine( H.hashInt fuid, H.hashInt guid )
                   )

    | ComComp hs  => foldl (fn (Hom(_,uid), acc ) =>
                             H.hashCombine(H.hashInt uid, acc)
                           )
                           (H.hashInt 795921317)
                           hs

    | Fixpoint ( Hom(_,uid) )  =>
        H.hashCombine( H.hashInt uid, H.hashInt 5959527)

    | Nested( Hom(_,uid), v ) =>
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
      val hshG = foldl (fn (Hom(_,uid), acc ) =>
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
      val hshG = foldl (fn (Hom(_,uid), acc ) =>
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
      val hshG = foldl (fn ( Hom(_,uid), acc ) =>
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
      val hshG = foldl (fn ( Hom(_,uid), acc ) =>
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

  fun toString (Hom(h,_)) =
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

structure UT = UnicityTableFunID2( structure Data = Definition )
structure HT = HashTable

(*--------------------------------------------------------------------------*)
type user = (UserIn -> UserOut) ref

(*--------------------------------------------------------------------------*)
fun funcValues (ref f) v =
  case f (FuncValues v ) of
    FuncValuesRes v => v
  | _               => raise NotFuncValues

(*--------------------------------------------------------------------------*)
fun inductiveValues (ref i) arc =
  case i (InductiveValues arc) of
    InductiveValuesRes h => h
  | _                    => raise NotInductiveValues

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
fun mkHom hom uid = Hom( hom, uid )

(*--------------------------------------------------------------------------*)
fun uid (Hom(_,x)) = x

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
fun domain ( Hom(h,_) ) =
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
fun isSelector (Hom((h,_))) =
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
  let
    val Hom(h1,_) = x
    val Hom(h2,_) = y
  in
    case ( h1, h2 ) of
      ( Nested( g1, v1 ), Nested( g2, v2) ) =>
        Variable.eq(v1,v2) andalso commutatives g1 g2
    | ( _, _ ) => false
  end

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
    case let val Hom(x,_) = h in x end of
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
  case let val Hom(x,_) = h in x end of

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

    fun addParameter xs (ry as (Hom(y,_))) =
    case y of

      ComComp ys  => foldl (fn (x,acc) => addParameter acc x) xs ys

    | Nested(f,v) =>
    let
      fun loop [] = [ry]
      |   loop ((rx as ( Hom(x,_)))::xs) =
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
      val (c,notC) = List.partition (fn x => commutatives x ry) xs
      fun mkComp x y = UT.unify( mkHom (Comp( x, y )) )
    in
      case notC of
        []  => ry::c
      | [x] => (mkComp x ry)::c
      | _   => (mkComp (mkCommutativeComposition notC) ry)::c
    end

  in
    case addParameter (addParameter [] x) y of
      [x] => x
    | xs  => mkCommutativeComposition xs
  end

(*--------------------------------------------------------------------------*)
fun mkFixpoint (rh as (Hom(h,_))) =
  case h of
    Id          => rh
  | Fixpoint _  => rh
  | _           => UT.unify( mkHom (Fixpoint rh) )

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
type result        = SDD
datatype operation = Op of hom * SDD * (operation -> result)

(*--------------------------------------------------------------------------*)
val eq' = eq
fun eq ( Op(xh,xsdd,_), Op(yh,ysdd,_) ) =
  eq'( xh, yh ) andalso SDD.eq( xsdd, ysdd )

(*--------------------------------------------------------------------------*)
fun hash (Op(Hom(_,uid),s,_)) =
  H.hashCombine( H.hashInt uid, SDD.hash s )

(*--------------------------------------------------------------------------*)
fun skipVariable var (Hom(h,_)) =
  case h of
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
fun evalCallback lookup h sdd =
  if SDD.empty sdd then
    SDD.zero
  else
    case let val Hom(x,_) = h in x end of
      Id                => sdd
    | Const c           => c
    | Cons(var,vl,next) => if eq'( next, id ) then
                                      SDD.node( var, vl, sdd )
                                    else
                                      lookup( Op( h, sdd, lookup ) )
    | _                 => lookup( Op( h, sdd, lookup ) )

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
fun hash ( Hom(_,uid), v ) =
  H.hashCombine( H.hashInt uid, Variable.hash v )

(*--------------------------------------------------------------------------*)
fun partition v hs =
let

  fun helper ( h, (F,G,L) ) =
    if skipVariable v h then
      ( h::F, G, L )
    else
      case let val Hom(x,_) = h in x end of
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

  case let val Hom(h,_) = f in h end of

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
  val (GSel,GNotSel) = List.partition isSelector G
in
  case Util.sort uid (op<) F of
    [] => orig
  | fs => mkSatComComp v (mkCommutativeComposition fs) (GSel@GNotSel)
end

(*--------------------------------------------------------------------------*)
fun apply ( h, v ) =
  case let val Hom(x,_) = h in x end of
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
  case let val Hom(x,_) = h in x end of
    Union _    => (eligible := !eligible + 1; rewriteCache.lookup (h,v))
  | Inter _    => (eligible := !eligible + 1; rewriteCache.lookup (h,v))
  | Fixpoint _ => (eligible := !eligible + 1; rewriteCache.lookup (h,v))
  | ComComp _  => (eligible := !eligible + 1; rewriteCache.lookup (h,v))
  | _          => h
end

(*--------------------------------------------------------------------------*)
(* Evaluate a list of homomorphisms and insert the result sorted into a list
   of results*)
fun evalInsert eval hs xs sdd =
  foldl (fn (h,acc) => SDD.insert acc (eval h sdd) ) xs hs

(*--------------------------------------------------------------------------*)
fun cons eval (var, vl, next) sdd =
  SDD.node( var, vl, eval next sdd )

(*--------------------------------------------------------------------------*)
fun union eval hs sdd =
  SDD.union( evalInsert eval hs [] sdd )

(*--------------------------------------------------------------------------*)
fun intersection eval hs sdd =
  SDD.intersection ( evalInsert eval hs [] sdd )

(*--------------------------------------------------------------------------*)
fun satUnion eval F G L sdd =
  if SDD.eq( sdd, SDD.one ) then
    raise DoNotPanic
  else
  let
    val fRes = case F of NONE => [] | SOME f => [eval f sdd]
    val gRes = evalInsert eval G fRes sdd
    val lRes = case L of NONE   => gRes
                       | SOME l => evalInsert eval [l] gRes sdd
  in
    SDD.union lRes
  end

(*--------------------------------------------------------------------------*)
fun satIntersection eval F G L sdd =
  if SDD.eq( sdd, SDD.one ) then
    raise DoNotPanic
  else
  let
    val fRes = case F of NONE => [] | SOME f => [eval f sdd]
    val gRes = evalInsert eval G fRes sdd
    val lRes = case L of NONE   => gRes
                       | SOME l => evalInsert eval [l] gRes sdd
  in
    SDD.intersection lRes
  end

(*--------------------------------------------------------------------------*)
fun composition eval a b sdd =
  eval a (eval b sdd)

(*--------------------------------------------------------------------------*)
fun commutativeComposition eval hs sdd =
  foldl (fn (h,acc) => eval h acc) sdd hs

(*--------------------------------------------------------------------------*)
fun satCommutativeComposition eval F G sdd =
  if SDD.eq( sdd, SDD.one ) then
    (* Standard composition *)
    foldl (fn (h,acc) => eval h acc) SDD.one (F::G)
  else
  let
    val fRes = eval F sdd
    val gRes = foldl (fn (g,acc) => eval g acc) fRes G
  in
    gRes
  end

(*--------------------------------------------------------------------------*)
local (* Fixpoint stuff *)

fun fixpointHelper f sdd =
let
  val res = f sdd
in
  if SDD.eq( res, sdd ) then
    res
  else
    fixpointHelper f res
end

in (* local fixpoint stuff *)

fun fixpoint eval h sdd =
  fixpointHelper (eval h) sdd

fun satFixpoint eval F G L sdd =
let
  fun loop sdd =
  let
    val r  = case F of NONE => sdd | SOME f => eval f sdd
    val r' = case L of NONE => r   | SOME l => eval l r
  in
    foldl (fn (g,sdd) => SDD.union[ sdd, eval g sdd ]) r' G
  end
in
  fixpointHelper loop sdd
end

end (* local fixpoint stuff *)

(*--------------------------------------------------------------------------*)
fun nested eval h var sdd =
  if SDD.eq( sdd, SDD.one ) then
    SDD.one

  (* skipVariable made nested propagated to the correct variable *)
  else if isSelector h then
     SDD.nodeAlpha( var
                  , map (fn ( vl, succ) =>
                          case vl of
                            SDD.Values _ => raise NestedHomOnValues
                          | SDD.Nested nvl =>
                              ( SDD.Nested (eval h nvl), succ )
                        )
                        (SDD.alpha sdd)
                  )
  else
    SDD.union (foldl
                (fn ( (vl,succ), acc ) =>
                  case vl of
                    SDD.Values _   => raise NestedHomOnValues
                  | SDD.Nested nvl =>
                    let
                      val nvl' = eval h nvl
                    in
                      SDD.insert acc (SDD.node( var, SDD.Nested nvl', succ))
                    end
                )
                []
                (SDD.alpha sdd)
              )

(*--------------------------------------------------------------------------*)
fun function f var sdd =
  if SDD.eq( sdd, SDD.one ) then
    SDD.one
  else if funcSelector f then
    SDD.nodeAlpha( var
                 , map (fn ( vl, succ) =>
                         case vl of
                           SDD.Nested _ => raise FunctionHomOnNested
                         | SDD.Values values =>
                             ( SDD.Values (funcValues f values), succ )
                       )
                       (SDD.alpha sdd)
                 )
  else
    SDD.union (foldl
                (fn ( (vl,succ), acc ) =>
                case vl of
                  SDD.Nested _      => raise FunctionHomOnNested
                | SDD.Values values =>
                let
                  val values' = funcValues f values
                in
                  SDD.insert acc (SDD.node( var, SDD.Values values', succ))
                end
                )
                []
                (SDD.alpha sdd)
              )

(*--------------------------------------------------------------------------*)
fun inductive eval i sdd =
  if SDD.eq( sdd, SDD.one ) then
    inductiveOne i
  else
  let
    val var = SDD.variable sdd
  in
    SDD.union (foldl (fn ( ( v, succ ), acc ) =>
                       case v of
                         SDD.Nested _  => raise Domain
                       | SDD.Values vl =>
                       let
                         val h = inductiveValues i (var,vl)
                       in
                         SDD.insert acc (eval h succ)
                       end
                     )
                     []
                     (SDD.alpha sdd)
              )
  end

(*--------------------------------------------------------------------------*)
val evals   = ref 0
val skipped = ref 0

(* Dispatch the evaluation of an homomorphism to the corresponding
   function. Used by CacheFun.
*)
fun apply ( Op( h, sdd, lookup) ) =
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
    in
      if isSelector h then
        SDD.nodeAlpha( var
                     , map (fn ( vl, succ) =>
                             ( vl, eval h succ )
                           )
                           (SDD.alpha sdd)
                     )
      else
        SDD.union (foldl (fn ( (vl, succ), acc ) =>
                         let
                           val succ' = eval h succ
                         in
                           SDD.insert acc (SDD.node( var, vl, succ'))
                         end
                         )
                         []
                         (SDD.alpha sdd)
                  )
    end
  else
  let
    val h' = rewrite h (SDD.variable sdd)
             handle SDD.IsNotANode => h
  in
    case let val Hom(x,_) = h' in x end of
      Id                    => raise DoNotPanic
    | Const _               => raise DoNotPanic
    | Cons(var,nested,next) => cons eval (var, nested, next) sdd
    | Union hs              => union eval hs sdd
    | Inter hs              => intersection eval hs sdd
    | Comp( a, b )          => composition eval a b sdd
    | ComComp hs            => commutativeComposition eval hs sdd
    | Fixpoint g            => fixpoint eval g sdd
    | Nested( g, var )      => nested eval g var sdd
    | Func( f, var )        => function f var sdd
    | Inductive i           => inductive eval i sdd
    | SatUnion( _, F, G, L) => satUnion eval F G L sdd
    | SatInter( _, F, G, L) => satIntersection eval F G L sdd
    | SatFixpoint(_,F,G,L)  => satFixpoint eval F G L sdd
    | SatComComp(_,F,G)     => satCommutativeComposition eval F G sdd
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
fun eval h sdd =
  if SDD.eq( sdd, SDD.zero ) then
    SDD.zero
  else
    case let val Hom(x,_) = h in x end of
      Id                => sdd
    | Const c           => c
    | Cons(var,vl,next) =>
      if eq( next, id ) then
        SDD.node( var, vl, sdd )
      else
        cache.lookup( Evaluation.Op( h, sdd, cacheLookup ) )
    | _ => cache.lookup( Evaluation.Op( h, sdd, cacheLookup ) )

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
  let
    val Hom(x,_) = h
  in
    case x of
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
  end

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
