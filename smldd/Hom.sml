(*--------------------------------------------------------------------------*)
signature HOM = sig

  eqtype hom
  type SDD
  type variable
  type values
  type valuation

  val id              : hom
  val mkCons          : variable -> valuation -> hom -> hom
  val mkConst         : SDD -> hom
  val mkUnion         : hom list -> hom
  val mkIntersection  : hom list -> hom
  val mkComposition   : hom -> hom -> hom
  val mkFixpoint      : hom -> hom
  val mkNested        : hom -> variable -> hom

  datatype UserIn     = Eval of values
                      | Hash
                      | Print

  datatype UserOut    = EvalRes  of values
                      | HashRes  of Hash.t
                      | PrintRes of string

  type userFunction   = (UserIn -> UserOut) ref

  val mkFunction      : userFunction -> variable -> hom

  val eval            : hom -> SDD -> SDD

  val toString        : hom -> string

  val stats           : unit -> string

  exception NestedHomOnValues
  exception FunctionHomOnNested
  exception EmptyOperands
  exception NotUserValues
  exception NotUserString
  exception NotUserHash

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
exception NotUserValues
exception NotUserString
exception NotUserHash

(*--------------------------------------------------------------------------*)
type SDD       = SDD.SDD
type variable  = Variable.t
type values    = Values.values
type valuation = SDD.valuation

(*--------------------------------------------------------------------------*)
datatype UserIn     = Eval of values
                    | Hash
                    | Print

(*--------------------------------------------------------------------------*)
datatype UserOut    = EvalRes  of values
                    | HashRes  of Hash.t
                    | PrintRes of string

(*--------------------------------------------------------------------------*)
fun funcValues (ref f) v =
  case f (Eval v ) of
    EvalRes v => v
  | _         => raise NotUserValues

(*--------------------------------------------------------------------------*)
fun funcString (ref f) =
  case f Print of
    PrintRes s => s
  | _          => raise NotUserString

(*--------------------------------------------------------------------------*)
fun funcHash (ref f) =
  case f Hash of
    HashRes h => h
  | _         => raise NotUserHash

(*--------------------------------------------------------------------------*)
structure Definition =
struct

  datatype t = Hom of ( hom * Hash.t * int )
  and hom    = Id
             | Cons        of ( variable * valuation * t ref )
             | Const       of SDD
             | Union       of t ref list
             | Inter       of t ref list
             | Comp        of ( t ref * t ref )
             | ComComp     of t ref list
             | Fixpoint    of ( t ref )
             | Nested      of ( t ref * variable )
             | Func        of ( (UserIn -> UserOut) ref * variable )
             | SatUnion    of ( variable
                              * (t ref) option
                              * t ref list
                              * (t ref) option )
             | SatInter    of ( variable
                              * (t ref) option    (* F *)
                              * t ref list        (* G *)
                              * (t ref) option )  (* L *)
             | SatFixpoint of ( variable
                              * (t ref) option    (* F *)
                              * t ref list        (* G *)
                              * (t ref) option )  (* L *)
             | SatComComp  of ( variable
                              * t ref             (* F *)
                              * t ref list        (* G *)
                              )

  fun eq (Hom(x,_,_),Hom(y,_,_)) =
    case (x,y) of
      ( Id, Id )                   => true
    | ( Cons(v,s,h), Cons(w,t,i))  => Variable.eq(v,w)
                                      andalso h=i
                                      andalso SDD.eqValuation(s,t)
    | ( Const s, Const t )         => s = t
    | ( Union xs, Union ys )       => xs = ys
    | ( Inter xs, Inter ys )       => xs = ys
    | ( Comp(a,b), Comp(c,d) )     => a = c andalso b = d
    | ( ComComp xs, ComComp ys )   => xs = ys
    | ( Fixpoint h, Fixpoint i )   => h = i
    | ( Nested(h,v), Nested(i,w) ) => h = i andalso Variable.eq(v,w)
    | ( Func(f,v), Func(g,w) )     => f = g andalso Variable.eq(v,w)
    | ( SatUnion(v, F, G, L)
      , SatUnion(v',F',G',L'))     => F = F' andalso G = G' andalso L = L'
                                      andalso Variable.eq(v,v')
    | ( SatInter(v, F, G, L)
      , SatInter(v',F',G',L'))     => F = F' andalso G = G' andalso L = L'
                                      andalso Variable.eq(v,v')
    | ( SatFixpoint(v, F, G, L)
      , SatFixpoint(v',F',G',L'))  => F = F' andalso G = G' andalso L = L'
                                      andalso Variable.eq(v,v')
    | ( SatComComp(v, F, G)
      , SatComComp(v',F',G'))      => Variable.eq(v,v') andalso F = F'
                                      andalso G = G'
    | ( _ , _ )                    => false

  fun hash (Hom(_,h,_)) = h

  fun toString (Hom(h,hsh,_)) =
  let
    fun optPartToString NONE      = ""
    |   optPartToString (SOME x) = toString (!x)
  in
  case h of
      Id          => "Id"
    | Cons(v,s,h) => "Cons(" ^ (Variable.toString v)
                             ^ ", "
                             ^ (SDD.valuationToString s)
                             ^ ", "
                             ^ (toString (!h))
                             ^ ")"
    | Const s     => "Const(" ^ (SDD.toString s) ^ ")"
    | Union hs    => String.concatWith " + "
                                       (map (fn h => toString (!h)) hs)
    | Inter hs    => String.concatWith " ^ "
                                       (map (fn h => toString (!h)) hs)
    | Comp(a,b)   => (toString (!a)) ^ " o " ^ (toString (!b))
    | ComComp hs  => String.concatWith " @ "
                                       (map (fn h => toString (!h)) hs)
    | Fixpoint h  => "(" ^ (toString (!h)) ^ ")*"
    | Nested(h,v) => "Nested(" ^ (toString (!h)) ^", "
                               ^ (Variable.toString v) ^ ")"
    | Func(_,v)   => "Func("  ^ ","
                      ^ (Variable.toString v) ^ ")"

    | SatUnion(_, F, G, L) =>    "F(" ^ (optPartToString F) ^ ") + "
                                ^ "G("
                                ^ (String.concatWith " + "
                                        (map (fn h => toString (!h)) G))
                                ^ ") + "
                                ^	"L(" ^ (optPartToString L) ^ ")"

    | SatInter(_, F, G, L) =>    "F(" ^ (optPartToString F) ^ ") ^ "
                                ^ "G("
                                ^ (String.concatWith " ^ "
                                        (map (fn h => toString (!h)) G))
                                ^ ") ^ "
                                ^	"L(" ^ (optPartToString L) ^ ")"

    | SatFixpoint(_, F, G, L) =>  "("
                                ^ "F(" ^ (optPartToString F) ^ ") + "
                                ^ "G("
                                ^ (String.concatWith " + "
                                        (map (fn h => toString (!h)) G))
                                ^ ") + "
                                ^	"L(" ^ (optPartToString L) ^ ") )*"

    | SatComComp(_, F, G) =>      "F(" ^ (toString (!F)) ^ ") @ "
                                ^ "G("
                                ^ (String.concatWith " @ "
                                        (map (fn h => toString (!h)) G))
                                ^ ")"
  end

end (* structure Definition *)
open Definition

(*--------------------------------------------------------------------------*)
type hom     = Definition.t ref

structure UT = UnicityTableFunID( structure Data = Definition )
structure H  = Hash
structure HT = HashTable

(*--------------------------------------------------------------------------*)
(* Called by the unicity table to construct an homomorphism with an id *)
fun mkHom hom hsh uid = Hom( hom, hsh, uid )

(*--------------------------------------------------------------------------*)
fun uid (ref(Hom(_,_,x))) = x

(*--------------------------------------------------------------------------*)
val id = UT.unify( mkHom Id (H.const 1) )

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
|   domainUnion (x::[])    = x
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
        l::(insert ls x)

    fun merge xs [] = xs
    |   merge xs (y::ys) =
      merge (insert xs y) ys

  in
    domainUnion ((Variables (merge ls rs))::xs)
  end

(*--------------------------------------------------------------------------*)
fun domain (ref(Hom((h,_,_)))) =
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
fun isSelector (ref(Hom((h,_,_)))) =
let
  fun selectorOption NONE     = true
  |   selectorOption (SOME h) = isSelector h
in
  case h of
    Func(_,_)            => true
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
    val ref(Hom(h1,_,_)) = x
    val ref(Hom(h2,_,_)) = y
  in
    case ( h1, h2 ) of
      ( Nested( g1, v1 ), Nested( g2, v2) ) =>
        Variable.eq(v1,v2) andalso commutatives g1 g2
    | ( _, _ ) => false
  end

(*--------------------------------------------------------------------------*)
fun mkCons var vl next =
let
  val hsh = H.hashCombine( Variable.hash var
              , H.hashCombine( SDD.hashValuation vl, hash (!next) ) )
in
  UT.unify( mkHom (Cons(var,vl,next)) hsh )
end

(*--------------------------------------------------------------------------*)
fun mkConst sdd =
let
  val hash = H.hashCombine( SDD.hash sdd, H.const 149199441 )
in
  UT.unify( mkHom (Const(sdd)) hash )
end

(*--------------------------------------------------------------------------*)
fun mkNested h vr =
  if h = id then
    id
  else
    UT.unify( mkHom (Nested(h,vr))
                    (H.hashCombine(hash (!h), Variable.hash vr )) )

(*--------------------------------------------------------------------------*)
structure HT = HashTable

fun mkUnion' []      = raise EmptyOperands
|   mkUnion' (x::[]) = x
|   mkUnion' xs      =
let

  (*val nesteds : ( ( variable , hom list ref ) HT.hash_table )
      = (HT.mkTable( Variable.hash , Variable.eq ) ( 10000, DoNotPanic ))*)

  fun unionHelper ( h, operands ) =
  case let val ref(Hom(x,_,_)) = h in x end of

    Union(ys)     => (foldl unionHelper [] ys) @ operands

  (*| Nested(g,v)   => (case HT.find nesteds v of
                       NONE    => HT.insert nesteds ( v, ref [g] )
                     | SOME hs => hs := !hs @ [g];
                     operands
                     )*)

  | _             => h::operands

  val operands = foldl unionHelper [] xs

  (*val nesteds' = HT.foldi (fn ( v, ref hs, acc) =>
                            (mkNested (mkUnion' hs) v) :: acc
                          )
                          []
                          nesteds*)
  val operands' = (*nesteds' @*) operands

  val unionHash = foldl (fn (x,acc) => H.hashCombine(hash (!x), acc))
                        (H.const 16564717)
                        operands'
in
  UT.unify( mkHom (Union operands') unionHash )
end

(*--------------------------------------------------------------------------*)
(* A sorting wrapper for mkUnion' which does the real job.
   Prefer mkUnion' for internal work. *)
val mkUnion = mkUnion' o (Util.sortUnique uid (op<) (op>))

(*--------------------------------------------------------------------------*)
fun mkIntersection []      = raise EmptyOperands
|   mkIntersection (x::[]) = x
|   mkIntersection xs      =
let
  val hsh = foldl (fn (x,acc) => H.hashCombine(hash (!x), acc))
                  (H.const 129292632)
                  xs
in
  UT.unify( mkHom (Inter xs) hsh )
end

(*--------------------------------------------------------------------------*)
fun mkCommutativeComposition [] = raise EmptyOperands
|   mkCommutativeComposition hs =
let
  val hs' = Util.sortUnique uid (op<) (op>) hs
  val hsh = foldl (fn (h,acc) => H.hashCombine(hash (!h), acc))
                  (H.const 795921317)
                  hs'
in
  UT.unify( mkHom (ComComp hs') hsh )
end

(*--------------------------------------------------------------------------*)
fun mkComposition x y =
  if y = id then
    x
  else if x = id then
    y
  else
  let

    fun addParameter xs (ry as (ref (Hom(y,_,_)))) =
    case y of

      ComComp ys  => foldl (fn (x,acc) => addParameter acc x) xs ys

    | Nested(f,v) =>
    let
      fun loop [] = [ry]
      |   loop ((rx as (ref(Hom(x,_,_))))::xs) =
       case x of
         Nested(g,w) => if Variable.eq( v, w ) then
                          (mkNested (mkComposition g f) v)::xs
                        else
                          rx::(loop xs)
       | _ => rx::(loop xs)
    in
      loop xs
    end

    | _ =>
    let
      val (c,notC) = List.partition (fn x => commutatives x ry) xs
      fun hsh x y = H.hashCombine( H.const 539351353
                                 , H.hashCombine( hash (!x), hash(!y) ) )
      fun mk x y = UT.unify( mkHom (Comp( x, y )) (hsh x y) )
    in
      case notC of
        []    => ry::c
      | x::[] => (mk x ry)::c
      | xs    => (mk (mkCommutativeComposition notC) ry)::c
    end

  in
    case addParameter (addParameter [] x) y of
      x::[] => x
    | xs    => mkCommutativeComposition xs
  end

(*--------------------------------------------------------------------------*)
fun mkFixpoint (rh as (ref (Hom(h,hsh,_)))) =
  case h of
    Id          => rh
  | Fixpoint _  => rh
  | _           => UT.unify( mkHom (Fixpoint(rh))
                                   (H.hashCombine( hsh, H.const 5959527)) )

(*--------------------------------------------------------------------------*)
fun mkFunction f var =
let
  val hsh = H.hashCombine( H.const 7837892,
              H.hashCombine( Variable.hash var, funcHash f ) )
in
  UT.unify( mkHom (Func(f,var)) hsh )
end

(*--------------------------------------------------------------------------*)
fun hashOption NONE           = H.const 183931413
|   hashOption (SOME (ref x)) = hash x

(*--------------------------------------------------------------------------*)
fun mkSatUnion var F G L =
let
  val hshG = foldl (fn (x,acc) => H.hashCombine(hash (!x), acc))
                   (H.const 59489417)
                   G
  val hsh = H.hashCombine( H.const 48511341
              , H.hashCombine( hashOption F
                 , H.hashCombine( hshG,
                     H.hashCombine(hashOption L, Variable.hash var ))))
in
  UT.unify( mkHom (SatUnion(var, F, G, L)) hsh )
end

(*--------------------------------------------------------------------------*)
fun mkSatIntersection var F G L =
let
  val hshG = foldl (fn (x,acc) => H.hashCombine(hash (!x), acc))
                   (H.const 565165613)
                   G
  val hsh = H.hashCombine( H.const 51454531
              , H.hashCombine( hashOption F
                 , H.hashCombine( hshG,
                     H.hashCombine(hashOption L, Variable.hash var ))))
in
  UT.unify( mkHom (SatInter(var, F, G, L)) hsh )
end

(*--------------------------------------------------------------------------*)
fun mkSatFixpoint var F G L =
let
  val hshG = foldl (fn (x,acc) => H.hashCombine(hash (!x), acc))
                   (H.const 19592927)
                   G
  val hsh = H.hashCombine( H.const 99495913
              , H.hashCombine( hashOption F
                 , H.hashCombine( hshG,
                     H.hashCombine(hashOption L, Variable.hash var ))))
in
  UT.unify( mkHom (SatFixpoint(var, F, G, L)) hsh )
end

(*--------------------------------------------------------------------------*)
fun mkSatComComp var F G =
let
  val G' = Util.sortUnique uid (op<) (op>) G
  val hshG = foldl (fn (x,acc) => H.hashCombine(hash (!x), acc))
                   (H.const 87284791)
                   G'
  val hsh = H.hashCombine( H.const 30918931
              , H.hashCombine( hash (!F)
                 , H.hashCombine( hshG, Variable.hash var )))
in
  UT.unify( mkHom (SatComComp(var, F, G' )) hsh )
end

(*--------------------------------------------------------------------------*)
structure Evaluation (* : OPERATION *) = struct

(*--------------------------------------------------------------------------*)
val name = "Hom"

(*--------------------------------------------------------------------------*)
type result        = SDD
datatype operation = Op of hom * SDD * (operation -> result)

(*--------------------------------------------------------------------------*)
fun eq ( Op(xh,xsdd,_), Op(yh,ysdd,_) ) =
  xh = yh andalso xsdd = ysdd

(*--------------------------------------------------------------------------*)
fun hash (Op(h,s,_)) =
  H.hashCombine( Definition.hash(!h), SDD.hash s )

(*--------------------------------------------------------------------------*)
fun skipVariable var (ref (Hom(h,_,_))) =
  case h of
    Id                   => true
  | Const _              => false
  | Cons(_,_,_)          => false
  | Nested(_,v)          => not (Variable.eq (var,v))
  | Union hs             => List.all (fn x => skipVariable var x) hs
  | Inter hs             => List.all (fn x => skipVariable var x) hs
  | Comp(a,b)            => skipVariable var a andalso skipVariable var b
  | ComComp hs           => List.all (fn x => skipVariable var x) hs
  | Fixpoint f           => skipVariable var f
  | Func(_,v)            => not (Variable.eq (var,v))
  | SatUnion(v,_,_,_)    => not (Variable.eq (var,v))
  | SatInter(v,_,_,_)    => not (Variable.eq (var,v))
  | SatFixpoint(v,_,_,_) => not (Variable.eq (var,v))
  | SatComComp(v,_,_)    => not (Variable.eq (var,v))

(*--------------------------------------------------------------------------*)
(* Evaluate an homomorphism on an SDD. Warning! Duplicate with Hom.eval! *)
fun evalCallback lookup h sdd =
  if sdd = SDD.zero then
    SDD.zero
  else
    case let val ref(Hom(x,_,_)) = h in x end of
      Id                => sdd
    | Const c           => c
    | Cons(var,vl,next) => if next = id then
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
val name = "Rewrite"

(*--------------------------------------------------------------------------*)
type operation = ( hom * variable )
type result    = hom

(*--------------------------------------------------------------------------*)
fun eq ((hx,vx),(hy,vy)) = hx = hy andalso Variable.eq(vx,vy)

(*--------------------------------------------------------------------------*)
fun hash (h,v) = H.hashCombine( Definition.hash(!h), Variable.hash v )

(*--------------------------------------------------------------------------*)
fun partition v hs =
let

  fun helper ( h, (F,G,L) ) =
    if skipVariable v h then
      ( h::F, G, L )
    else
      case let val ref(Hom(x,_,_)) = h in x end of
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

  case let val ref(Hom(h,_,_)) = f in h end of

    Union xs =>
      if List.exists (fn x => x = id) xs then
      let
        val (F,G,L) = partition v xs
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
          mkSatFixpoint v F' G L'
        end
      end

      else (* No id in operands*)
        orig

  | _ => orig

(*--------------------------------------------------------------------------*)
fun rewriteComComp orig v hs =
let
  val (F,G) = List.partition (fn h => skipVariable v h ) hs
in
  case Util.sortUnique uid (op<) (op>) F of
    [] => orig
  | fs => mkSatComComp v (mkCommutativeComposition fs) G
end

(*--------------------------------------------------------------------------*)
fun apply ( h, v ) =
  case let val ref(Hom(x,_,_)) = h in x end of
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
  case let val ref(Hom(x,_,_)) = h in x end of
    Union _    => (eligible := !eligible + 1; rewriteCache.lookup (h,v))
  | Inter _    => (eligible := !eligible + 1; rewriteCache.lookup (h,v))
  | Fixpoint _ => (eligible := !eligible + 1; rewriteCache.lookup (h,v))
  | ComComp _  => (eligible := !eligible + 1; rewriteCache.lookup (h,v))
  | _          => h
end

(*--------------------------------------------------------------------------*)
(* Evaluate a list of homomorphisms and insert the result sorted into a list
   of results*)
fun evalInsert lookup hs xs sdd =
  foldl (fn (h,acc) => SDD.insert acc (evalCallback lookup h sdd) ) xs hs

(*--------------------------------------------------------------------------*)
fun cons lookup (var, vl, next) sdd =
  SDD.node( var, vl, evalCallback lookup next sdd )

(*--------------------------------------------------------------------------*)
fun union lookup hs sdd =
  SDD.union( evalInsert lookup hs [] sdd )

(*--------------------------------------------------------------------------*)
fun intersection lookup hs sdd =
  SDD.intersection ( evalInsert lookup hs [] sdd )

(*--------------------------------------------------------------------------*)
fun satUnion lookup F G L sdd =
  if sdd = SDD.one then
    raise DoNotPanic
  else
  let
    val fRes = case F of NONE => [] | SOME f => [evalCallback lookup f sdd]
    val gRes = evalInsert lookup G fRes sdd
    val lRes = case L of NONE   => gRes
                       | SOME l => evalInsert lookup [l] gRes sdd
  in
    SDD.union lRes
  end

(*--------------------------------------------------------------------------*)
fun satIntersection lookup F G L sdd =
  if sdd = SDD.one then
    raise DoNotPanic
  else
  let
    val fRes = case F of NONE => [] | SOME f => [evalCallback lookup f sdd]
    val gRes = evalInsert lookup G fRes sdd
    val lRes = case L of NONE   => gRes
                       | SOME l => evalInsert lookup [l] gRes sdd
  in
    SDD.intersection lRes
  end

(*--------------------------------------------------------------------------*)
fun composition lookup a b sdd =
  evalCallback lookup a (evalCallback lookup b sdd)

(*--------------------------------------------------------------------------*)
fun commutativeComposition lookup hs sdd =
  foldr (fn (h,acc) => evalCallback lookup h acc) sdd hs

(*--------------------------------------------------------------------------*)
fun satCommutativeComposition lookup F G sdd =
  if sdd = SDD.one then
    (* Standard composition *)
    foldr (fn (h,acc) => evalCallback lookup h acc) SDD.one (F::G)
  else
  let
    val fRes = evalCallback lookup F sdd
    val gRes = foldr (fn (g,acc) => evalCallback lookup g acc) fRes G
  in
    gRes
  end

(*--------------------------------------------------------------------------*)
fun fixpointHelper f sdd =
let
  val res = f sdd
in
  if res = sdd then
    res
  else
    fixpointHelper f res
end

(*--------------------------------------------------------------------------*)
fun fixpoint lookup h sdd =
  fixpointHelper (evalCallback lookup h) sdd

(*--------------------------------------------------------------------------*)
fun satFixpoint lookup F G L sdd =
let
  fun loop sdd =
  let
    val r  = case F of NONE => sdd | SOME f => evalCallback lookup f sdd
    val r' = case L of NONE => r   | SOME l => evalCallback lookup l r
  in
    foldl (fn (g,sdd) => SDD.union[ sdd, evalCallback lookup g sdd ]) r' G
  end
in
  fixpointHelper loop sdd
end

(*--------------------------------------------------------------------------*)
fun nested lookup h var sdd =
  if sdd = SDD.one then
    SDD.one
  else (* skipVariable made nested propagated to the correct variable *)
  let
    val res = foldl
              (fn ( (vl,succ), acc ) =>
                case vl of
                  SDD.Values(_)   => raise NestedHomOnValues
                | SDD.Nested(nvl) =>
                  let
                    val nvl' = evalCallback lookup h nvl
                  in
                    SDD.insert acc (SDD.node( var, SDD.Nested nvl', succ))
                  end
              )
              []
              (SDD.alpha sdd)
  in
    SDD.union res
  end

(*--------------------------------------------------------------------------*)
fun function lookup f var sdd =
  if sdd = SDD.one then
    SDD.one
  else
  let
    val res = foldl
              (fn ( (vl,succ), acc ) =>
              case vl of
                SDD.Nested(_)      => raise FunctionHomOnNested
              | SDD.Values(values) =>
              let
                val values' = funcValues f values
              in
                SDD.insert acc (SDD.node( var, SDD.Values values', succ))
              end
              )
              []
              (SDD.alpha sdd)
  in
    SDD.union res
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
in
  if skip then
    let
      val _ = skipped := !skipped + 1
      val var = SDD.variable sdd
      val res =
        foldl
        (fn ( (vl, succ), acc ) =>
        let
          val succ' = evalCallback lookup h succ
        in
          SDD.insert acc (SDD.node( var, vl, succ'))
        end
        )
        []
        (SDD.alpha sdd)
    in
      SDD.union res
    end
  else
  let
    val h' = rewrite h (SDD.variable sdd)
             handle SDD.IsNotANode => h
  in
    case let val ref(Hom(x,_,_)) = h' in x end of
      Id                    => raise DoNotPanic
    | Const _               => raise DoNotPanic
    | Cons(var,nested,next) => cons lookup (var, nested, next) sdd
    | Union hs              => union lookup hs sdd
    | Inter hs              => intersection lookup hs sdd
    | Comp( a, b )          => composition lookup a b sdd
    | ComComp hs            => commutativeComposition lookup hs sdd
    | Fixpoint g            => fixpoint lookup g sdd
    | Nested( g, var )      => nested lookup g var sdd
    | Func( f, var )        => function lookup f var sdd
    | SatUnion( _, F, G, L) => satUnion lookup F G L sdd
    | SatInter( _, F, G, L) => satIntersection lookup F G L sdd
    | SatFixpoint(_,F,G,L)  => satFixpoint lookup F G L sdd
    | SatComComp(_,F,G)     => satCommutativeComposition lookup F G sdd
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
  if sdd = SDD.zero then
    SDD.zero
  else
    case let val ref(Hom(x,_,_)) = h in x end of
      Id                => sdd
    | Const c           => c
    | Cons(var,vl,next) =>
      if next = id then
        SDD.node( var, vl, sdd )
      else
        cache.lookup( Evaluation.Op( h, sdd, cacheLookup ) )
    | _ => cache.lookup( Evaluation.Op( h, sdd, cacheLookup ) )

(*--------------------------------------------------------------------------*)
fun toString x = Definition.toString (!x)

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
