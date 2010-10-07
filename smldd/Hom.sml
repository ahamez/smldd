(*--------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------*)

signature Hom =
sig

  eqtype hom
  type SDD
  type variable
  type valuation

  (*datatype userFunction = Func of { apply : valuation -> valuation
                      , eq    : userFunction * userFunction -> bool 
                      , hash  : userFunction -> Word32.word
                      }*)

  val id            : hom
  val cons          : variable -> SDD -> hom -> hom
  val flatCons      : variable -> valuation -> hom -> hom
  val const         : SDD -> hom
  val union         : hom list -> hom
  val composition   : hom -> hom -> hom
  val fixpoint      : hom -> hom
  val nested        : hom -> variable -> hom
  (*val function      : userFunction -> hom*)

  val eval          : hom -> SDD -> SDD

  exception NotYetImplemented

end

(*--------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------*)

functor HomFun ( structure SDD : SDD
                 and Variable  : VARIABLE  where type t = SDD.variable
                 and Valuation : VALUATION where type t = SDD.valuation
               )
  : Hom
= struct

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  exception NotYetImplemented
  exception DoNotPanic

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  type SDD       = SDD.SDD
  type variable  = Variable.t
  type valuation = Valuation.t

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  structure Definition =
  struct

    datatype t = Hom of ( hom * Word32.word )
    and hom    = Id
               | Cons     of ( variable * SDD * t ref )
               | FlatCons of ( variable * valuation * t ref )
               | Const    of SDD
               | Union    of t ref list
               | Compo    of ( t ref * t ref )
               | Fixpoint of ( t ref )
               | Nested   of ( t ref * variable )
               (*| Function of ( )*)

    fun eq (Hom(x,_),Hom(y,_)) =
    case x of
      Id => (case y of Id => true | _ => false ) 
    | Cons(v,s,h) => (case y of 
                        Cons(w,t,i) => Variable.eq(v,w) andalso s=t andalso h=i
                     | _ => false )
    | FlatCons(v,s,h) => (case y of
                            FlatCons(w,t,i) => Variable.eq(v,w) 
                              andalso Valuation.eq(s,t) andalso h=i
                         | _ => false )
    | Const(s) => (case y of Const(t) => s = t | _ => false)
    | Union(xs) => (case y of Union(ys) => xs = ys | _ =>false)
    | Compo(a,b) => (case y of Compo(c,d) => a=c andalso b=d | _ => false)
    | Fixpoint(h) => (case y of Fixpoint(i) => h=i | _ => false)
    | Nested(h,v) => (case y of Nested(i,w) => h=i andalso Variable.eq(v,w)
                                | _ => false)
    
    fun hash (Hom(_,h)) = h

  end (* structure Definition *)
  open Definition

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  type hom = Definition.t ref
  structure UT = UnicityTableFun( structure Data = Definition )

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  val id = UT.unify( Hom(Id,MLton.hash 1) )

  fun cons var nested next =
  let
    val hash = Word32.xorb( Variable.hash var
                 , Word32.xorb( SDD.hash nested, hash (!next) ) )
  in
    UT.unify( Hom( Cons(var,nested,next), hash ))
  end

  fun flatCons var vl next =
  let
    val hash = Word32.xorb( Variable.hash var
                 , Word32.xorb( Valuation.hash vl, hash (!next) ) )
  in
    UT.unify( Hom( FlatCons(var,vl,next), hash ))
  end

  fun const sdd =
  let
    val hash = Word32.xorb( SDD.hash sdd, Word32.fromInt 149199441 )
  in
    UT.unify( Hom( Const(sdd), hash ))
  end

  fun union xs = raise NotYetImplemented
  
  fun composition x y = raise NotYetImplemented

  fun fixpoint x = raise NotYetImplemented

  fun nested h vr = raise NotYetImplemented

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

  local (* Homomorphisms evaluation *)

  structure Evaluation (* : OPERATION *) =
  struct

    type result        = SDD
    datatype operation = Op of hom * SDD * (operation -> result)

    fun eq ( Op(xh,xsdd,_), Op(yh,ysdd,_) ) =
      xh = yh andalso xsdd = ysdd

    fun hash (Op(h,s,_)) =
      Word32.xorb( Definition.hash(!h), SDD.hash s )

    (* Evaluate an homomorphism on an SDD
       Warning! Duplicate logic with Hom.eval!
    *)
    fun evalCallback lookup ( hom, sdd ) =
    case !hom of
      Hom( Id, _ )       => sdd
    | Hom( Const(c), _ ) => c
    | _                  => lookup( Op( hom, sdd, lookup ) )

    fun cons lookup (var, nested, next) sdd =
      SDD.node( var, nested, evalCallback lookup (next, sdd ) )

    fun flatCons lookup (var, vl, next) sdd =
      SDD.flatNode( var, vl, evalCallback lookup (next, sdd ) )

    fun apply ( Op( h, sdd, lookup) ) =
    case !h of
      Hom( Id, _ )    => raise DoNotPanic
    | Hom(Const(_),_) => raise DoNotPanic

    | Hom(Cons(var,nested,next),_)
      => cons lookup (var, nested, next) sdd

    | Hom(FlatCons(var,vl,next),_)
      => flatCons lookup (var, vl, next) sdd

    | _               => raise NotYetImplemented

  end (* structure Evaluation *)

  structure cache = CacheFun(structure Operation = Evaluation)

  val cacheLookup = cache.lookup

  in (* local Homomorphisms evaluation *)

  (* Evaluate an homomorphism on an SDD *)
  fun eval h sdd =
  case !h of
    Hom( Id, _ )       => sdd
  | Hom( Const(c), _ ) => c
  | _                  => cache.lookup( Evaluation.Op( h, sdd, cacheLookup ) )
    
  end (* local Homomorphisms evaluation *)

  (*----------------------------------------------------------------------*)
  (*----------------------------------------------------------------------*)

end (* functor HomFun *)

(*--------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------*)

structure Hom = HomFun( structure SDD       = SDD
                      ; structure Variable  = IntVariable
                      ; structure Valuation = DiscreteIntValuation
                      )

(*--------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------*)
