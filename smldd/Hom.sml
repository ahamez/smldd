(*--------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------*)

signature Hom =
sig

  eqtype hom
  type SDD
  type variable
  type values
  type valuation

  val id              : hom
  val mkCons          : variable -> valuation -> hom -> hom
  val mkConst         : SDD -> hom
  val mkUnion         : hom list -> hom
  val mkComposition   : hom -> hom -> hom
  val mkFixpoint      : hom -> hom
  val mkNested        : hom -> variable -> hom
  val mkFunction      : (values -> values) ref -> variable -> hom

  val eval            : hom -> SDD -> SDD

  val toString        : hom -> string

  val stats           : unit -> string

  exception NotYetImplemented
  exception NestedHomOnValues
  exception FunctionHomOnNested

end

(*--------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------*)

functor HomFun ( structure SDD : SDD
                 and Variable  : VARIABLE where type t = SDD.variable
                 and Values    : VALUES   where type stored = SDD.storedValues
                                          where type user   = SDD.userValues
               )
  : Hom
= struct

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  exception NotYetImplemented
  exception NestedHomOnValues
  exception FunctionHomOnNested

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  type SDD       = SDD.SDD
  type variable  = Variable.t
  type values    = Values.user
  type valuation = SDD.valuation

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  structure Definition =
  struct

    datatype t = Hom of ( hom * Hash.t )
    and hom    = Id
               | Cons     of ( variable * valuation * t ref )
               | Const    of SDD
               | Union    of t ref list
               | Compo    of ( t ref * t ref )
               | Fixpoint of ( t ref )
               | Nested   of ( t ref * variable )
               | Func     of ( (values -> values) ref * variable )

    fun eq (Hom(x,_),Hom(y,_)) =
      case (x,y) of
        ( Id, Id )                   => true
      | ( Cons(v,s,h), Cons(w,t,i))  => Variable.eq(v,w)
                                        andalso h=i
                                        andalso SDD.eqValuation(s,t)
      | ( Const(s), Const(t) )       => s = t
      | ( Union(xs), Union(ys) )     => xs = ys
      | ( Compo(a,b), Compo(c,d) )   => a = c andalso b = d
      | ( Fixpoint(h), Fixpoint(i) ) => h = i
      | ( Nested(h,v), Nested(i,w) ) => h = i andalso Variable.eq(v,w)
      | ( Func(f,v), Func(g,w) )     => f = g andalso Variable.eq(v,w)
      | ( _ , _ )                    => false

    fun hash (Hom(_,h)) = h

    fun toString (Hom(h,hsh)) =
      (*"#"
         ^ (H.toString hsh)
         ^ " [ "
         ^ *)
    (case h of
        Id          => "Id"
      | Cons(v,s,h) => "Cons(" ^ (Variable.toString v)
                               ^ ", "
                               ^ (SDD.valuationToString s)
                               ^ ", "
                               ^ (toString (!h))
                               ^ ")"
      | Const(s)    => "Const(" ^ (SDD.toString s) ^ ")"
      | Union(hs)   => String.concatWith " + " (map (fn h => toString (!h)) hs)
      | Compo(a,b)  => (toString (!a)) ^ " o " ^ (toString (!b))
      | Fixpoint(h) => "(" ^ (toString (!h)) ^ ")*"
      | Nested(h,v) => "Nested(" ^ (toString (!h)) ^", "
                                 ^ (Variable.toString v) ^ ")"
      | Func(_,v)   => "Func(" ^ (Variable.toString v) ^ ")"
      )
    (*^ " ] "*)
  end (* structure Definition *)
  open Definition

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  type hom     = Definition.t ref

  structure UT = UnicityTableFun( structure Data = Definition )
  structure H  = Hash
  structure HT = HashTable

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  val id = UT.unify( Hom(Id,H.const 1) )

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  fun mkCons var vl next =
  let
    val hsh = H.hashCombine( Variable.hash var
                , H.hashCombine( SDD.hashValuation vl, hash (!next) ) )
  in
    UT.unify( Hom( Cons(var,vl,next), hsh ))
  end

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  fun mkConst sdd =
  let
    val hash = H.hashCombine( SDD.hash sdd, H.const 149199441 )
  in
    UT.unify( Hom( Const(sdd), hash ))
  end

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  fun mkNested h vr =
  if h = id then
    id
  else
    UT.unify( Hom( Nested(h,vr), H.hashCombine(hash (!h), Variable.hash vr )))

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  fun mkUnion xs =
  case xs of
    []    => mkConst SDD.zero
  | x::[] => x
  | _     =>
    let

      val locals : (( variable, hom list ref ) HT.hash_table) ref
          = ref (HT.mkTable( fn x => Variable.hash x , Variable.eq )
                          ( 10000, DoNotPanic ))

      fun unionHelper ( h, operands ) =
      case let val ref(Hom(x,_)) = h in x end of
        Union(ys)     => (foldl unionHelper [] ys) @ operands
      | Nested(i,var) =>
        (case HT.find (!locals) var of
          NONE       => HT.insert (!locals) ( var, ref [i] )
        | SOME hList => hList := h::(!hList);
        operands
        )
      | _ => h::operands

      val unionLocals = map (fn (var,xs) => mkNested (mkUnion (!xs)) var)
                            (HT.listItemsi(!locals))

      val operands = (foldl unionHelper [] xs) @ unionLocals

      val unionHash = foldl (fn (x,acc) => H.hashCombine(hash (!x), acc))
                            (H.const 16564717)
                            operands
    in
      UT.unify( Hom( Union(operands), unionHash ) )
    end

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)
  
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
    UT.unify( Hom( Compo( x, y ), hsh ) )
  end

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  fun mkFixpoint (rh as (ref (Hom(h,hsh)))) =
  case h of
    Id          => rh
  | Fixpoint(_) => rh
  | _           => UT.unify( Hom( Fixpoint(rh)
                                , H.hashCombine( hsh, H.const 5959527) )
                           )

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  fun mkFunction f var =
  let
    val hsh = H.hashCombine( H.const 7837892, Variable.hash var )
  in
    UT.unify( Hom( Func(f,var), hsh ) )
  end

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  local (* Homomorphisms evaluation *)

  structure Evaluation (* : OPERATION *) =
  struct

    val name = "Hom"

    (*--------------------------------------------------------------------*)
    (*--------------------------------------------------------------------*)

    type result        = SDD
    datatype operation = Op of hom * SDD * (operation -> result)

    (*--------------------------------------------------------------------*)
    (*--------------------------------------------------------------------*)

    fun eq ( Op(xh,xsdd,_), Op(yh,ysdd,_) ) =
      xh = yh andalso xsdd = ysdd

    (*--------------------------------------------------------------------*)
    (*--------------------------------------------------------------------*)

    fun hash (Op(h,s,_)) =
      H.hashCombine( Definition.hash(!h), SDD.hash s )

    (*--------------------------------------------------------------------*)
    (*--------------------------------------------------------------------*)

    fun skipVariable var (ref (Hom(h,_))) =
    case h of
      Id          => true
    | Const(_)    => false
    | Cons(_,_,_) => false
    | Nested(_,v) => not (Variable.eq (var,v))
    | Union(xs)   => List.all (fn x => skipVariable var x) xs
    | Compo(a,b)  => skipVariable var a andalso skipVariable var b
    | Fixpoint(f) => skipVariable var f
    | Func(_,v)   => not (Variable.eq (var,v))

    (*--------------------------------------------------------------------*)
    (*--------------------------------------------------------------------*)

    (* Evaluate an homomorphism on an SDD.
       Warning! Duplicate logic with Hom.eval!
    *)
    fun evalCallback lookup h sdd =
    if sdd = SDD.zero then
      SDD.zero
    else
      case let val ref(Hom(x,_)) = h in x end of
        Id                => sdd
      | Const(c)          => c
      | Cons(var,vl,next) => if next = id then
                                        SDD.node( var, vl, sdd )
                                      else
                                        lookup( Op( h, sdd, lookup ) )
      | _                 => lookup( Op( h, sdd, lookup ) )

    (*--------------------------------------------------------------------*)
    (*--------------------------------------------------------------------*)

    fun cons lookup (var, vl, next) sdd =
      SDD.node( var, vl, evalCallback lookup next sdd )

    (*--------------------------------------------------------------------*)
    (*--------------------------------------------------------------------*)

    fun union lookup xs sdd =
    if sdd = SDD.one then
      SDD.union (map (fn x => evalCallback lookup x sdd ) xs)
    else
    let
      (*val res = map (fn x => evalCallback lookup x sdd ) xs*)
      val var = SDD.variable sdd
      val (F,G) = List.partition (skipVariable var) xs
      val fRes = evalCallback lookup (mkUnion F) sdd
      val gRes = map (fn x => evalCallback lookup x sdd ) G
    in
      SDD.union (fRes::gRes)
    end

    (*--------------------------------------------------------------------*)
    (*--------------------------------------------------------------------*)

    fun composition lookup a b sdd =
      evalCallback lookup a (evalCallback lookup b sdd)

    (*--------------------------------------------------------------------*)
    (*--------------------------------------------------------------------*)

    fun fixpoint lookup h sdd =
    let

      val (saturate,xs) =
        case !h of
          Hom(Union(xs),_) => ( List.exists (fn x => x = id) xs, SOME xs )
        | _ => ( false, NONE )

      fun fixpointHelper f sdd =
      let
        val res = f sdd
      in
        if res = sdd then
          res
        else
          fixpointHelper f res
      end

    in

      if sdd = SDD.one orelse not saturate then
        fixpointHelper (evalCallback lookup h) sdd

      else
      let
        val var = SDD.variable sdd
        val (F,G) = List.partition (skipVariable var) (valOf(xs))
        fun loop sdd =
        let
          val resF = evalCallback lookup (mkFixpoint (mkUnion (id::F))) sdd
        in
          foldl (fn (g,sdd) => SDD.union[sdd,evalCallback lookup g sdd])
                resF
                G
        end
      in
        fixpointHelper loop sdd
      end

    end

    (*--------------------------------------------------------------------*)
    (*--------------------------------------------------------------------*)

    fun nested lookup h var sdd =
    if sdd = SDD.one then
      SDD.one
    else if sdd = SDD.zero then
      SDD.zero
    else (* skipVariable made nested propagated to the correct variable *)
    let
      val res = map
                (fn (vl,succ) =>
                  case vl of
                    SDD.Values(_)   => raise NestedHomOnValues
                  | SDD.Nested(nvl) =>
                    let
                      val nvl' = evalCallback lookup h nvl
                    in
                      SDD.node( var, SDD.Nested nvl', succ)
                    end
                )
                (SDD.alpha sdd)
    in
      SDD.union res
    end

    (*--------------------------------------------------------------------*)
    (*--------------------------------------------------------------------*)

    fun function lookup f var sdd =
    if sdd = SDD.one then
      SDD.one
    else if sdd = SDD.zero then
      SDD.zero
    else
    let
      val res = map
                (fn (vl,succ) =>
                case vl of
                  SDD.Nested(_)      => raise FunctionHomOnNested
                | SDD.Values(values) =>
                let
                  val values' = !f values
                in
                  SDD.node( var, SDD.Values values', succ)
                end
                )
                (SDD.alpha sdd)
    in
      SDD.union res
    end

    (*--------------------------------------------------------------------*)
    (*--------------------------------------------------------------------*)
    (* Dispatch the evaluation of an homomorphism to the corresponding
       function. Used by CacheFun.
    *)
    fun apply ( Op( h, sdd, lookup) ) =
    let
      val skip = let val v = SDD.variable sdd in skipVariable v h end
                 handle SDD.IsNotANode => false
    in
      if skip then
        let
          val var = SDD.variable sdd
          val res =
            map
            (fn (vl, succ) =>
            let
              val succ' = evalCallback lookup h succ
            in
              SDD.node( var, vl, succ')
            end
            )
            (SDD.alpha sdd)
        in
          SDD.union res
        end
      else
        case let val ref(Hom(x,_)) = h in x end of

          Id                    => raise DoNotPanic
        | Const(_)              => raise DoNotPanic
        | Cons(var,nested,next) => cons lookup (var, nested, next) sdd
        | Union(xs)             => union lookup xs sdd
        | Compo( a, b )         => composition lookup a b sdd
        | Fixpoint(g)           => fixpoint lookup g sdd
        | Nested( g, var )      => nested lookup g var sdd
        | Func( f, var )        => function lookup f var sdd

    end

    (*--------------------------------------------------------------------*)
    (*--------------------------------------------------------------------*)

  end (* structure Evaluation *)

  in (* local Homomorphisms evaluation *)

  structure cache = CacheFun(structure Operation = Evaluation)
  val cacheLookup = cache.lookup

  (* Evaluate an homomorphism on an SDD.
     Warning! Duplicate logic with Evaluation.evalCallback!
  *)
  fun eval h sdd =
  if sdd = SDD.zero then
    SDD.zero
  else
    case let val ref(Hom(x,_)) = h in x end of
      Id                => sdd
    | Const(c)          => c
    | Cons(var,vl,next) =>
      if next = id then
        SDD.node( var, vl, sdd )
      else
        cache.lookup( Evaluation.Op( h, sdd, cacheLookup ) )
    | _ => cache.lookup( Evaluation.Op( h, sdd, cacheLookup ) )

  end (* local Homomorphisms evaluation *)

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  fun toString x = Definition.toString (!x)

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  fun stats () = cache.stats()

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

end (* functor HomFun *)

(*--------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------*)
