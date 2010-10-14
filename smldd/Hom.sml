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
                 and Values    : VALUES   where type t = SDD.values
               )
  : Hom
= struct

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  exception NotYetImplemented
  exception NestedHomOnValues
  exception FunctionHomOnNested
  exception DoNotPanic

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  type SDD       = SDD.SDD
  type variable  = Variable.t
  type values    = Values.t
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
    case x of
      Id          => (case y of Id => true | _ => false )
    | Cons(v,s,h) => (case y of
                        Cons(w,t,i) => Variable.eq(v,w)
                                       andalso SDD.eqValuation(s,t)
                                       andalso h=i
                      | _ => false)
    | Const(s)    => (case y of Const(t)    => s = t | _ => false)
    | Union(xs)   => (case y of Union(ys)   => xs = ys | _ =>false)
    | Compo(a,b)  => (case y of Compo(c,d)  => a=c andalso b=d | _ => false)
    | Fixpoint(h) => (case y of Fixpoint(i) => h=i | _ => false)
    | Nested(h,v) => (case y of Nested(i,w) => h=i andalso Variable.eq(v,w)
                              | _ => false)
    | Func(f,v)   => (case y of Func(g,w) => Variable.eq(v,w) andalso f = g
                                | _ => false
                     )

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

  val id = UT.unify( Hom(Id,MLton.hash 1) )

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  fun mkCons var vl next =
  let
    val hash = H.hashCombine( Variable.hash var
                 , H.hashCombine( SDD.hashValuation vl, hash (!next) ) )
  in
    UT.unify( Hom( Cons(var,vl,next), hash ))
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
      case !h of
        Hom( Union(ys), _ )     => (foldl unionHelper [] ys) @ operands
      | Hom( Nested(h,var), _ ) =>
        (case HT.find (!locals) var of
          NONE       => HT.insert (!locals) ( var, ref [h] )
        | SOME hList => hList := h::(!hList);
        operands
        )
      | _                       => h::operands

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

  fun mkFixpoint x =
  case !x of
    Hom( Id, _ )          => x
  | Hom( Fixpoint(_), _ ) => x
  | _ => UT.unify( Hom( Fixpoint(x)
                      , H.hashCombine(hash (!x), H.const 5959527)))

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

    fun skipVariable (var, hom) =
    case !hom of
      Hom( Id, _ )          => true
    | Hom( Const(_), _ )    => false
    | Hom( Cons(_,_,_), _ ) => false
    | Hom( Nested(_,v),_)   => not (Variable.eq (var,v))
    | Hom( Union(xs),_)     => List.all (fn x => skipVariable(var,x)) xs
    | Hom( Compo(a,b),_)    => skipVariable(var,a) andalso skipVariable(var,b)
    | Hom( Fixpoint(f),_)   => skipVariable(var,f)
    | Hom( Func(_,v),_)     => not (Variable.eq (var,v))

    (*--------------------------------------------------------------------*)
    (*--------------------------------------------------------------------*)

    (* Evaluate an homomorphism on an SDD.
       Warning! Duplicate logic with Hom.eval!
    *)
    fun evalCallback lookup h sdd =
    if sdd = SDD.zero then
      SDD.zero
    else
      case !h of
        Hom( Id, _ )       => sdd
      | Hom( Const(c), _ ) => c
      | Hom( Cons(var,vl,next), _) => if next = id then
                                        SDD.node( var, vl, sdd )
                                      else
                                        lookup( Op( h, sdd, lookup ) )
      | _ => lookup( Op( h, sdd, lookup ) )

    (*--------------------------------------------------------------------*)
    (*--------------------------------------------------------------------*)

    fun cons lookup (var, vl, next) sdd =
      SDD.node( var, vl, evalCallback lookup next sdd )

    (*--------------------------------------------------------------------*)
    (*--------------------------------------------------------------------*)

    fun union lookup xs sdd =
    let
      val res = map (fn x => evalCallback lookup x sdd ) xs
    in
      SDD.union res
    end

    (*--------------------------------------------------------------------*)
    (*--------------------------------------------------------------------*)

    fun composition lookup a b sdd =
      evalCallback lookup a (evalCallback lookup b sdd)

    (*--------------------------------------------------------------------*)
    (*--------------------------------------------------------------------*)

    fun fixpoint lookup h sdd =
    let
      (* Should we avoid caching inner evaluations? *)
      val res = evalCallback lookup h sdd
    in
      if res = sdd then
        res
      else
        fixpoint lookup h res
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
      val skip = let val v = SDD.variable sdd in skipVariable (v,h) end
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
        case !h of

          Hom( Id, _ )    => raise DoNotPanic
        | Hom(Const(_),_) => raise DoNotPanic

        | Hom(Cons(var,nested,next),_)
          => cons lookup (var, nested, next) sdd

        | Hom( Union(xs),_ )
          => union lookup xs sdd

        | Hom( Compo( a, b ), _ )
          => composition lookup a b sdd

        | Hom( Fixpoint(g), _ )
          => fixpoint lookup g sdd

        | Hom( Nested( g, var ), _ )
          => nested lookup g var sdd

        | Hom( Func( f, var ), _ )
          => function lookup f var sdd

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
    case !h of
      Hom( Id, _ )       => sdd
    | Hom( Const(c), _ ) => c
    | Hom( Cons(var,vl,next), _) =>
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

structure Hom = HomFun( structure SDD      = SDD
                      ; structure Variable = IntVariable
                      ; structure Values   = DiscreteIntValues
                      )

(*--------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------*)
