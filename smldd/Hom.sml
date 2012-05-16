(*--------------------------------------------------------------------------*)
signature HOM = sig

  type hom
  type SDD
  type variable
  type values
  type valuation

  (* Tell if two homomorphisms are equals. Constant time. *)
  val eq              : hom * hom -> bool
  (* Return the unique identifier of an homomorphism. Warning, uids are
     recycled! *)
  val uid             : hom -> int

  (* Identity homomorphism: return the SDD on which it's applied *)
  val id              : hom
  (* Always return |0| whatever is its argument when applied *)
  val zero            : hom
  (* Always return |1| whatever is its argument when applied *)
  val one             : hom
  (* Return the SDD var --(vl)--> x where x is the result of the application
     of h on the SDD to which the cons operation is applied *)
  val mkCons          : variable -> valuation -> hom -> hom
  (* Always return the SDD given at its construction whatever is its
     argument on which it's applied *)
  val mkConst         : SDD -> hom
  val mkUnion         : hom list -> hom
  val mkIntersection  : hom list -> hom
  val mkComposition   : hom -> hom -> hom
  val mkFixpoint      : hom -> hom
  val mkNested        : hom -> variable -> hom

  datatype UserIn       = InValues of (variable * values)
                        | InInductiveOne
                        | InHash
                        | InPrint

  datatype UserOut      = OutInductiveValues of hom
                        | OutInductiveOne of SDD
                        | OutHash of Hash.t
                        | OutPrint of string

  type user           = (UserIn -> UserOut) ref

  val mkInductive     : user -> hom

  (* Evaluate an homomorphism on an SDD. *)
  val eval            : hom -> SDD -> SDD
  (* Export an homomorphism to a string. *)
  val toString        : hom -> string
  (* Export some statistics as a string. *)
  val stats           : unit -> string

  type 'a visitor     =
                     (*Id*)    (unit -> 'a)
                   (*Cons*) -> (variable -> valuation -> hom -> 'a)
                  (*Const*) -> (SDD -> 'a)
                  (*Union*) -> (hom list -> 'a)
           (*Intersection*) -> (hom list -> 'a)
            (*Composition*) -> (hom -> hom -> 'a)
               (*Fixpoint*) -> (hom -> 'a)
                 (*Nested*) -> (hom -> variable -> 'a)
              (*Inductive*) -> (user -> 'a)
                            -> hom
                            -> 'a
  val mkVisitor       : unit -> 'a visitor

  exception NestedHomOnValues
  exception EmptyOperands
  exception NotOutHash
  exception NotOutPrint
  exception NotOutInductiveValues
  exception NotOutInductiveOne

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
exception EmptyOperands
exception NotOutHash
exception NotOutPrint
exception NotOutInductiveValues
exception NotOutInductiveOne

(*--------------------------------------------------------------------------*)
type SDD       = SDD.SDD
type variable  = Variable.t
type values    = Values.values
type valuation = SDD.valuation

(*--------------------------------------------------------------------------*)
structure Definition (* : DATA *) = struct

  structure H = Hash

  datatype hom = Id
               | Cons        of variable * valuation * t
               | Const       of SDD
               | Union       of t list
               | Inter       of t list
               | Comp        of t * t
               | Fixpoint    of t
               | Nested      of t * variable
               | Inductive   of (UserIn -> UserOut) ref

  and UserIn  = InValues of (variable * values)
              | InInductiveOne
              | InHash
              | InPrint

  and UserOut = OutInductiveValues of t
              | OutInductiveOne of SDD
              | OutHash of Hash.t
              | OutPrint of string

  (* int -> uid of an homomorphism. Generated by the hash table. *)
  withtype t = (hom * int)

  fun funcString (ref f) =
    (case f InPrint of
      OutPrint s => s
    | _          => "???"
    )
    handle Match => "???"

  fun funcHash (ref f) =
    case f InHash of
      OutHash h => h
    | _         => raise NotOutHash

  (* Compare two homomorphisms. Only used by the hash table for unicity. *)
  fun eq ( (x,_), (y,_) ) =
  let
    fun eqList ([], [])       = true
    |   eqList ([], _ )       = false
    |   eqList ( _, [])       = false
    |   eqList (x::xs, y::ys) = if eq(x, y) then eqList(xs, ys) else false

    fun eqOption (NONE, NONE)     = true
    |   eqOption (NONE, _   )     = false
    |   eqOption (_   , NONE)     = false
    |   eqOption (SOME x, SOME y) = eq(x, y)

  in
    case (x, y) of
      (Id, Id )                   => true
    | (Cons(v,s,h), Cons(w,t,i))  => Variable.eq(v, w)
                                     andalso eq(h, i)
                                     andalso SDD.eqValuation(s, t)
    | (Const s, Const t)          => SDD.eq(s, t)
    | (Union xs, Union ys)        => eqList(xs, ys)
    | (Inter xs, Inter ys)        => eqList(xs, ys)
    | (Comp(a,b), Comp(c,d))      => eq(a, c) andalso eq(b, d)
    | (Fixpoint h, Fixpoint i)    => eq(h, i)
    | (Nested(h,v), Nested(i,w))  => eq(h, i) andalso Variable.eq(v, w)
    | (Inductive i, Inductive j)  => i = j
    | (_ , _)                     => false
  end

  fun hash (h,_) =
  let
    fun hashOption NONE           = H.hashInt 183931413
    |   hashOption (SOME (_,uid)) = H.hashInt uid
  in
    case h of
      Id          => H.hashInt 1

    | Cons(v, s, (_,uid)) =>
      H.hashCombine( Variable.hash v
                   , H.hashCombine(SDD.hashValuation s, H.hashInt uid))

    | Const s     => H.hashCombine(SDD.hash s, H.hashInt 149199441)

    | Union hs    => foldl (fn ((_,uid),acc) =>
                             H.hashCombine(H.hashInt uid, acc)
                           )
                           (H.hashInt 16564717)
                           hs

    | Inter hs    => foldl (fn ((_,uid), acc) =>
                             H.hashCombine(H.hashInt uid, acc)
                           )
                           (H.hashInt 129292632)
                           hs

    | Comp( (_,fuid), (_,guid) ) =>
      H.hashCombine( H.hashInt 3413417
                   , H.hashCombine( H.hashInt fuid, H.hashInt guid )
                   )

    | Fixpoint (_,uid) =>
        H.hashCombine( H.hashInt uid, H.hashInt 5959527)

    | Nested( (_,uid), v ) =>
        H.hashCombine(H.hashInt uid, Variable.hash v )

    | Inductive i => H.hashCombine( H.hashInt 42429527
                                  , funcHash i
                                  )
  end

  fun toString (h,_) =
  let
    fun optPartToString NONE     = ""
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
    | Fixpoint h  => "(" ^ (toString h) ^ ")*"
    | Nested(h,v) => "Nested(" ^ (toString h) ^", "
                               ^ (Variable.toString v) ^ ")"
    | Inductive i => "Inductive(" ^ (funcString i) ^ ")"
  end

  (* Called by the unicity table to configure itself *)
  fun configure UnicityTableConfiguration.Name =
    UnicityTableConfiguration.NameRes "Hom"
  |   configure UnicityTableConfiguration.Buckets =
    UnicityTableConfiguration.BucketsRes 10000

end (* structure Definition *)
open Definition

(*--------------------------------------------------------------------------*)
type hom     = Definition.t

structure UT = UnicityTableFunID(structure Data = Definition)
structure HT = HashTable

(*--------------------------------------------------------------------------*)
type user = (UserIn -> UserOut) ref

(*--------------------------------------------------------------------------*)
fun inductiveValues (ref i) param =
  case i (InValues param) of
    OutInductiveValues h => h
  | _                    => raise NotOutInductiveValues

(*--------------------------------------------------------------------------*)
fun inductiveOne (ref i) =
  case i InInductiveOne of
    OutInductiveOne s => s
  | _                 => raise NotOutInductiveOne

(*--------------------------------------------------------------------------*)
(* Called by the unicity table to construct an homomorphism with an id *)
fun mkHom hom uid = (hom, uid)

(*--------------------------------------------------------------------------*)
fun uid (_,x) = x

(*--------------------------------------------------------------------------*)
fun eq (h1,h2) = uid h1 = uid h2

(*--------------------------------------------------------------------------*)
val id = UT.unify(mkHom Id)

(*--------------------------------------------------------------------------*)
fun mkCons var vl next =
  UT.unify(mkHom (Cons(var,vl,next)))

(*--------------------------------------------------------------------------*)
fun mkConst sdd =
  UT.unify(mkHom (Const(sdd)))

(*--------------------------------------------------------------------------*)
val zero = mkConst SDD.zero
val one  = mkConst SDD.one

(*--------------------------------------------------------------------------*)
fun mkNested h vr =
  if eq(h, id) then
    id
  else
    UT.unify( mkHom (Nested(h,vr)) )

(*--------------------------------------------------------------------------*)
fun mkUnion []  = raise EmptyOperands
|   mkUnion [x] = x
|   mkUnion xs  = UT.unify(mkHom(Union xs))

(*--------------------------------------------------------------------------*)
fun mkIntersection []  = raise EmptyOperands
|   mkIntersection [x] = x
|   mkIntersection xs  = UT.unify( mkHom (Inter xs) )

(*--------------------------------------------------------------------------*)
fun mkComposition x y =
  if eq(y, id) then
    x
  else if eq(x, id) then
    y
  else
    UT.unify( mkHom (Comp( x, y )) )

(*--------------------------------------------------------------------------*)
fun mkFixpoint h =
  case #1 h of
    Id          => h
  | Fixpoint _  => h
  | _           => UT.unify( mkHom (Fixpoint h) )

(*--------------------------------------------------------------------------*)
fun mkInductive i =
  UT.unify(mkHom (Inductive i))

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
fun hash (Op( (_,uid), s, _ ) ) =
  H.hashCombine( H.hashInt uid, SDD.hash s )

(*--------------------------------------------------------------------------*)
(* Evaluate an homomorphism on an SDD. Warning! Duplicate with Hom.eval! *)
fun evalCallback lookup h sdd =
  if SDD.empty sdd then
    SDD.zero
  else
    case #1 h of
      Id                  => sdd
    | Const c             => c
    | Cons(var, vl, next) => if eq'(next, id) then
                               SDD.node (var, vl, sdd)
                             else
                               lookup (Op (h, sdd, lookup))
    | _                   => lookup(Op(h, sdd, lookup))

(*--------------------------------------------------------------------------*)
(* Evaluate a list of homomorphisms and insert the result sorted into a list
   of results*)
fun evalInsert eval hs xs sdd =
  foldl (fn (h,acc) => SDD.insert acc (eval h sdd) ) xs hs

(*--------------------------------------------------------------------------*)
fun cons eval (var, vl, next) sdd =
  SDD.node(var, vl, eval next sdd)

(*--------------------------------------------------------------------------*)
fun union eval hs sdd =
  SDD.union(evalInsert eval hs [] sdd)

(*--------------------------------------------------------------------------*)
fun intersection eval hs sdd =
let
  fun loop res [] = res
  |   loop res (h::hs) =
  let
    val tmp = eval h sdd
  in
    if SDD.eq(tmp, SDD.zero) then
      []
    else
      loop (SDD.insert res tmp) hs
  end
in
  SDD.intersection(loop [] hs)
end

(*--------------------------------------------------------------------------*)
fun composition eval a b sdd =
  eval a (eval b sdd)

(*--------------------------------------------------------------------------*)
local (* Fixpoint stuff *)

fun fixpointHelper f sdd =
let
  val res = f sdd
in
  if SDD.eq(res, sdd) then
    res
  else
    fixpointHelper f res
end

in (* local fixpoint stuff *)

fun fixpoint eval h sdd =
  fixpointHelper (eval h) sdd

end (* local fixpoint stuff *)

(*--------------------------------------------------------------------------*)
fun nested eval h var sdd =
  if SDD.eq (sdd, SDD.one) then
    SDD.one

  else
    SDD.union (foldl
                (fn ( (vl,succ), acc ) =>
                  case vl of
                    SDD.Values _   => raise NestedHomOnValues
                  | SDD.Nested nvl =>
                    let
                      val nvl' = eval h nvl
                    in
                      SDD.insert acc (SDD.node (var, SDD.Nested nvl', succ))
                    end
                )
                []
                (SDD.alpha sdd)
              )

(*--------------------------------------------------------------------------*)
fun inductive eval i sdd =
  if SDD.eq (sdd, SDD.one) then
    inductiveOne i
  else
  let
    val var = SDD.variable sdd
  in
    SDD.union (foldl (fn ((v, succ), acc) =>
                       case v of
                         SDD.Nested _  => raise Domain
                       | SDD.Values values =>
                       let
                         val h = inductiveValues i (var, values)
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

(* Dispatch the evaluation of an homomorphism to the corresponding
   function. Used by CacheFun.
*)
fun apply (Op(h, sdd, lookup)) =
let
  val _ = evals := !evals + 1
  val eval = evalCallback lookup
in
  case #1 h of
     (* Id and Const evaluation aren't cached *)
    Id                    => raise DoNotPanic
  | Const _               => raise DoNotPanic
  | Cons(var,nested,next) => cons eval (var, nested, next) sdd
  | Union hs              => union eval hs sdd
  | Inter hs              => intersection eval hs sdd
  | Comp(a, b)            => composition eval a b sdd
  | Fixpoint g            => fixpoint eval g sdd
  | Nested( g, var )      => nested eval g var sdd
  | Inductive i           => inductive eval i sdd
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
  if SDD.eq (sdd, SDD.zero) then
    SDD.zero
  else
    case #1 h of
      Id                 => sdd
    | Const c            => c
    | Cons (var,vl,next) => if eq (next, id) then
                              SDD.node (var, vl, sdd)
                            else
                              cache.lookup(Evaluation.Op(h, sdd, cacheLookup))
    | _ => cache.lookup(Evaluation.Op (h, sdd, cacheLookup))

(*--------------------------------------------------------------------------*)
type 'a visitor =
                     (*Id*)    (unit -> 'a)
                   (*Cons*) -> (variable -> valuation -> hom -> 'a)
                  (*Const*) -> (SDD -> 'a)
                  (*Union*) -> (hom list -> 'a)
           (*Intersection*) -> (hom list -> 'a)
            (*Composition*) -> (hom -> hom -> 'a)
               (*Fixpoint*) -> (hom -> 'a)
                 (*Nested*) -> (hom -> variable -> 'a)
              (*Inductive*) -> (user -> 'a)
                            -> hom
                            -> 'a

(*--------------------------------------------------------------------------*)
fun mkVisitor (():unit) : 'a visitor =
let

  fun visitor id cons const union inter comp fixpoint nested inductive h
  =
    case #1 h of
      Id               => id ()
    | Cons(v, vl, nxt) => cons v vl nxt
    | Const s          => const s
    | Union hs         => union hs
    | Inter hs         => inter hs
    | Comp(a, b)       => comp a b
    | Fixpoint h       => fixpoint h
    | Nested(h, v)     => nested h v
    | Inductive i      => inductive i

in
  visitor
end

(*--------------------------------------------------------------------------*)
fun stats () = (cache.stats())
               ^ "\n-----------------\n"
               ^ "Homomorphisms\n"
               ^ "evals: " ^ (Int.toString (!Evaluation.evals))
               ^ "\n"

(*--------------------------------------------------------------------------*)
end (* functor HomFun *)
