(*--------------------------------------------------------------------------*)
signature Hom = sig

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
  val mkFunction      : (values -> values) ref -> variable -> hom

  val eval            : hom -> SDD -> SDD

  val toString        : hom -> string

  val stats           : unit -> string

  exception NestedHomOnValues
  exception FunctionHomOnNested

end

(*--------------------------------------------------------------------------*)
functor HomFun ( structure SDD : SDD
                 and Variable  : VARIABLE where type t      = SDD.variable
                 and Values    : VALUES   where type values = SDD.values
               )
  : Hom
= struct

(*--------------------------------------------------------------------------*)
exception NestedHomOnValues
exception FunctionHomOnNested

(*--------------------------------------------------------------------------*)
type SDD       = SDD.SDD
type variable  = Variable.t
type values    = Values.values
type valuation = SDD.valuation

(*--------------------------------------------------------------------------*)
structure Definition =
struct

  datatype t = Hom of ( hom * Hash.t * int )
  and hom    = Id
             | Cons        of ( variable * valuation * t ref )
             | Const       of SDD
             | Union       of t ref list
             | Inter       of t ref list
             | Compo       of ( t ref * t ref )
             | Fixpoint    of ( t ref )
             | Nested      of ( t ref * variable )
             | Func        of ( (values -> values) ref * variable )
             | SatUnion    of ( variable * t ref * t ref list * t ref )
             | SatFixpoint of ( variable * t ref * t ref list * t ref )

  fun eq (Hom(x,_,_),Hom(y,_,_)) =
    case (x,y) of
      ( Id, Id )                   => true
    | ( Cons(v,s,h), Cons(w,t,i))  => Variable.eq(v,w)
                                      andalso h=i
                                      andalso SDD.eqValuation(s,t)
    | ( Const(s), Const(t) )       => s = t
    | ( Union(xs), Union(ys) )     => xs = ys
    | ( Inter(xs), Inter(ys) )     => xs = ys
    | ( Compo(a,b), Compo(c,d) )   => a = c andalso b = d
    | ( Fixpoint(h), Fixpoint(i) ) => h = i
    | ( Nested(h,v), Nested(i,w) ) => h = i andalso Variable.eq(v,w)
    | ( Func(f,v), Func(g,w) )     => f = g andalso Variable.eq(v,w)
    | ( SatUnion(v, F, G, L)
      , SatUnion(v',F',G',L'))     => F = F' andalso G = G' andalso L = L'
                                      andalso Variable.eq(v,v')
    | ( SatFixpoint(v, F, G, L)
      , SatFixpoint(v',F',G',L'))  => F = F' andalso G = G' andalso L = L'
                                      andalso Variable.eq(v,v')
    | ( _ , _ )                    => false

  fun hash (Hom(_,h,_)) = h

  fun toString (Hom(h,hsh,_)) =
  case h of
      Id          => "Id"
    | Cons(v,s,h) => "Cons(" ^ (Variable.toString v)
                             ^ ", "
                             ^ (SDD.valuationToString s)
                             ^ ", "
                             ^ (toString (!h))
                             ^ ")"
    | Const(s)    => "Const(" ^ (SDD.toString s) ^ ")"
    | Union(hs)   => String.concatWith " + "
                                       (map (fn h => toString (!h)) hs)
    | Inter(hs)   => String.concatWith " ^ "
                                       (map (fn h => toString (!h)) hs)
    | Compo(a,b)  => (toString (!a)) ^ " o " ^ (toString (!b))
    | Fixpoint(h) => "(" ^ (toString (!h)) ^ ")*"
    | Nested(h,v) => "Nested(" ^ (toString (!h)) ^", "
                               ^ (Variable.toString v) ^ ")"
    | Func(_,v)   => "Func(" ^ (Variable.toString v) ^ ")"
    | SatUnion(_, F, G, L) =>    "F(" ^ (toString (!F)) ^ ") + "
                                ^ "G("
                                ^ (String.concatWith " + "
                                        (map (fn h => toString (!h)) G))
                                ^ ") + "
                                ^	"L(" ^ (toString (!L)) ^ ")"
    | SatFixpoint(_, F, G, L) =>  "("
                                ^ "F(" ^ (toString (!F)) ^ ") + "
                                ^ "G("
                                ^ (String.concatWith " + "
                                        (map (fn h => toString (!h)) G))
                                ^ ") + "
                                ^	"L(" ^ (toString (!L)) ^ ") )*"

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
fun mkUnion' xs =
  case xs of
    []    => id
  | x::[] => x
  | _     =>
    let

      fun unionHelper ( h, operands ) =
      case let val ref(Hom(x,_,_)) = h in x end of
        Union(ys)     => (foldl unionHelper [] ys) @ operands
      | _             => h::operands

      val operands = foldl unionHelper [] xs

      val unionHash = foldl (fn (x,acc) => H.hashCombine(hash (!x), acc))
                            (H.const 16564717)
                            operands
    in
      UT.unify( mkHom (Union(operands)) unionHash )
    end

(*--------------------------------------------------------------------------*)
(* A sorting wrapper for mkUnion' which does the real job.
   Prefer mkUnion' for internal work. *)
val mkUnion = mkUnion' o (Util.sortUnique uid (op<) (op>))

(*--------------------------------------------------------------------------*)
fun mkIntersection [] = id
|   mkIntersection (x::[]) = x
|   mkIntersection xs =
let
  val hsh = foldl (fn (x,acc) => H.hashCombine(hash (!x), acc))
                  (H.const 129292632)
                  xs
in
  UT.unify( mkHom (Inter(xs)) hsh )
end

(*--------------------------------------------------------------------------*)
fun mkComposition x y =
  if x = id then
    y
  else if y = id then
    x
  else
  let
    val hsh = H.hashCombine( H.const 539351353
                           , H.hashCombine( hash (!x), hash(!y) ) )
  in
    UT.unify( mkHom (Compo( x, y )) hsh  )
  end

(*--------------------------------------------------------------------------*)
fun mkFixpoint (rh as (ref (Hom(h,hsh,_)))) =
  case h of
    Id          => rh
  | Fixpoint(_) => rh
  | _           => UT.unify( mkHom (Fixpoint(rh))
                                   (H.hashCombine( hsh, H.const 5959527)) )

(*--------------------------------------------------------------------------*)
fun mkFunction f var =
let
  val hsh = H.hashCombine( H.const 7837892, Variable.hash var )
in
  UT.unify( mkHom (Func(f,var)) hsh )
end

(*--------------------------------------------------------------------------*)
fun mkSatUnion var F G L =
let
  val hshG = foldl (fn (x,acc) => H.hashCombine(hash (!x), acc))
                   (H.const 59489417)
                   G
  val hsh = H.hashCombine( H.const 48511341
              , H.hashCombine( hash(!F)
                 , H.hashCombine( hshG,
                     H.hashCombine(hash(!L), Variable.hash var ))))
in
  UT.unify( mkHom (SatUnion(var, F, G, L)) hsh )
end

(*--------------------------------------------------------------------------*)
fun mkSatFixpoint var F G L =
let
  val hshG = foldl (fn (x,acc) => H.hashCombine(hash (!x), acc))
                   (H.const 19592927)
                   G
  val hsh = H.hashCombine( H.const 99495913
              , H.hashCombine( hash(!F)
                 , H.hashCombine( hshG,
                     H.hashCombine(hash(!L), Variable.hash var ))))
in
  UT.unify( mkHom (SatFixpoint(var, F, G, L)) hsh )
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
  | Const(_)             => false
  | Cons(_,_,_)          => false
  | Nested(_,v)          => not (Variable.eq (var,v))
  | Union(xs)            => List.all (fn x => skipVariable var x) xs
  | Inter(xs)            => List.all (fn x => skipVariable var x) xs
  | Compo(a,b)           => skipVariable var a andalso skipVariable var b
  | Fixpoint(f)          => skipVariable var f
  | Func(_,v)            => not (Variable.eq (var,v))
  | SatUnion(v,_,_,_)    => not (Variable.eq (var,v))
  | SatFixpoint(v,_,_,_) => not (Variable.eq (var,v))

(*--------------------------------------------------------------------------*)
(* Evaluate an homomorphism on an SDD. Warning! Duplicate with Hom.eval! *)
fun evalCallback lookup h sdd =
  if sdd = SDD.zero then
    SDD.zero
  else
    case let val ref(Hom(x,_,_)) = h in x end of
      Id                => sdd
    | Const(c)          => c
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
fun partition v ( h, (F,G,L) ) =
  if skipVariable v h then
    ( h::F, G, L )
  else
    case let val ref(Hom(x,_,_)) = h in x end of
      Nested(n,_) => ( F, G, n::L )
    | _           => ( F, h::G, L )

(*--------------------------------------------------------------------------*)
fun rewriteUnion orig v xs =
let
  val (F,G,L) = foldr (partition v) ([],[],[]) xs
in
  if length F = 0 andalso length L = 0 then
    orig
  else
    (
    rewritten := !rewritten + 1;
    mkSatUnion v (mkUnion' F) G (mkNested (mkUnion' L) v)
    )
end

(*--------------------------------------------------------------------------*)
fun rewriteFixpoint orig v f =
  case let val ref(Hom(h,_,_)) = f in h end of
    Union(xs) =>
      if List.exists (fn x => x = id) xs then
        let
          val (F,G,L) = foldr (partition v) ([],[],[]) xs
        in
          if length F = 0 andalso length L = 0 then
            orig
          else
            (
            rewritten := !rewritten + 1;
            mkSatFixpoint v
                          (mkFixpoint(mkUnion' F))
                          G
                          (mkNested (mkFixpoint (mkUnion' (id::L))) v)
            )
        end
      else
        orig
  | _ => orig

(* ------------------------------------------------ *)
fun apply ( h, v ) =
  case let val ref(Hom(x,_,_)) = h in x end of
    Union(xs)   => rewriteUnion h v xs
  | Fixpoint(f) => rewriteFixpoint h v f
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
    Union(xs)   => (eligible := !eligible + 1; rewriteCache.lookup (h,v))
  | Fixpoint(f) => (eligible := !eligible + 1; rewriteCache.lookup (h,v))
  | _           => h
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
    SDD.union ( evalInsert lookup (F::L::G) [] sdd )

(*--------------------------------------------------------------------------*)
fun composition lookup a b sdd =
  evalCallback lookup a (evalCallback lookup b sdd)

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
    val r  = evalCallback lookup F sdd
    val r' = evalCallback lookup L r
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
                val values' = !f values
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
    | Const(_)              => raise DoNotPanic
    | Cons(var,nested,next) => cons lookup (var, nested, next) sdd
    | Union(xs)             => union lookup xs sdd
    | Inter(xs)             => intersection lookup xs sdd
    | Compo( a, b )         => composition lookup a b sdd
    | Fixpoint(g)           => fixpoint lookup g sdd
    | Nested( g, var )      => nested lookup g var sdd
    | Func( f, var )        => function lookup f var sdd
    | SatUnion( _, F, G, L) => satUnion lookup F G L sdd
    | SatFixpoint(_,F,G,L)  => satFixpoint lookup F G L sdd
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
    | Const(c)          => c
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
