(*--------------------------------------------------------------------------*)
signature TOOLS = sig

  type SDD
  type hom

  datatype mode  = Sharing | Hierarchy

  val nbPaths    : SDD -> IntInf.int
  val nbNodes    : mode -> SDD -> LargeInt.int
  val toDot      : mode -> SDD -> string

  val homToDot   : hom -> string

end (* signature TOOLS *)

(*--------------------------------------------------------------------------*)
functor ToolsFun ( structure SDD : SDD
                   and Variable  : VARIABLE where type t      = SDD.variable
                   and Values    : VALUES   where type values = SDD.values
                   and Hom       : HOM      where type SDD = SDD.SDD
                                            where type variable = SDD.variable
                                            where type values = SDD.values
                 )
  : TOOLS
= struct

(*--------------------------------------------------------------------------*)
type SDD = SDD.SDD
type hom = Hom.hom

(*--------------------------------------------------------------------------*)
datatype mode = Sharing | Hierarchy

(*--------------------------------------------------------------------------*)
structure HT = HashTable

(*--------------------------------------------------------------------------*)
(* Count the number of distinct paths in an SDD *)
fun nbPaths x =
let

  fun zero () = IntInf.fromInt 0
  fun one  () = IntInf.fromInt 1

  val visit = SDD.mkVisitor SDD.Cached zero one

  fun node _ _ alpha =
    foldl (fn ( (vl,succ) , nb) =>
            case vl of
              SDD.Values v => nb +   (IntInf.fromInt (Values.length v))
                                   * visit node succ
            | SDD.Nested n => nb +   visit node n
                                   * visit node succ
          )
          (IntInf.fromInt 0)
          alpha

in
  visit node x
end (* fun visitNbPaths *)

(*--------------------------------------------------------------------------*)
fun nbNodes mode x =
let

  fun zero () = LargeInt.fromInt 1
  fun one  () = LargeInt.fromInt 1

  val visit =
    case mode of
      Sharing   => SDD.mkVisitor (SDD.Once (LargeInt.fromInt 0)) zero one
    | Hierarchy => SDD.mkVisitor SDD.Cached zero one

  fun node _ _ alpha =
    (LargeInt.fromInt 1)
  + (foldl (fn ( (vl,succ), sum ) =>
             sum
           + (case vl of
               SDD.Values v => 0
             | SDD.Nested n => visit node n
             )
           + visit node succ
           )
          (LargeInt.fromInt 0)
          alpha
        )
in
  visit node x
end

(*--------------------------------------------------------------------------*)
(* Export an SDD to a DOT representation *)
fun toDotHelper mode x =
let

  val visit = case mode of Hierarchy => SDD.mkVisitor SDD.NonCached
                         | Sharing   => SDD.mkVisitor (SDD.Once [])

  val visitArc = SDD.mkVisitor SDD.NonCached

  val maxShare = case mode of Hierarchy => false
                            | Sharing   => true

  fun depthStr depth = if maxShare then
                         ""
                       else
                         "_" ^ (Int.toString depth)

  fun terminal value depth =
      "terminal"
    ^ (Int.toString value)
    ^ (depthStr depth)
    ^ " [shape=rectangle,regular=true,label=\""
    ^ (Int.toString value)
    ^ "\"];\n"

  fun node depth dotHelper uid var alpha =
      "\"node"
    ^ (Int.toString uid)
    ^ (depthStr depth)
    ^ "\" [shape=circle,label=\""
    ^ (Variable.toString var)
    ^ "\"];\n"
    :: (foldl (fn ((vl,succ),str) =>
                case vl of
                  SDD.Values v => str @ (dotHelper succ depth)
                | SDD.Nested n => str
                                  @ (dotHelper n    (depth + 1) )
                                  @ (dotHelper succ depth       )
              )
              []
              alpha
       )

  fun walkOnly depth dotHelper uid var alpha =
    foldl (fn ((vl,succ),str) =>
              case vl of
                SDD.Values v => dotHelper succ depth
              | SDD.Nested n => str
                                @ (dotHelper n    (depth + 1) )
                                @ (dotHelper succ depth       )
          )
          []
          alpha

  (* Associate an SDD to a list of all hierarchies it belongs to *)
  val nodes : ( ( SDD , int list ref ) HT.hash_table )
        = (HT.mkTable( SDD.hash , op = ) ( 10000, DoNotPanic ))

  val maxDepth = ref 0

  fun dotHelper sdd depth =
  let
    val ( found, newDepth ) =
                case HT.find nodes sdd of
                  NONE        => ( HT.insert nodes ( sdd, ref [depth] );
                                   ( false, false )
                                 )
                | SOME depths =>
                  let
                    fun insertSorted x [] = ([x] , true)
                    |   insertSorted x (Y as (y::ys)) =
                      if x = y then
                        ( Y, false )
                      else if x < y then
                        ( x::Y, true )
                      else
                      let
                        val (ys',newDepth) = insertSorted x ys
                      in
                        ( y::ys', newDepth )
                      end

                    val ( depths', newDepth ) = insertSorted depth (!depths)
                    val _ = depths := depths'
                  in
                    ( true, newDepth )
                  end
    val _ = if depth > !maxDepth then
              maxDepth := depth
            else
              ()
  in
    if not found then
      visit (fn () => []) (fn () => []) (node depth dotHelper) sdd
    else if newDepth then
      visit (fn () => []) (fn () => []) (walkOnly depth dotHelper) sdd
    else
      []
  end

  fun nodeArc depth uid _ alpha =
  let

    fun nodeStr uid depth =
      "\"node" ^ (Int.toString uid) ^ (depthStr depth) ^ "\""

    val curr = nodeStr uid depth
    val visitString = SDD.mkVisitor SDD.NonCached

  in
    foldl ( fn ( (vl,succ), str ) =>
          let

            fun helper depth sdd =
              visitString (fn () => raise DoNotPanic)
                          (fn () => "terminal1" ^ (depthStr depth))
                          (fn x => fn _ => fn _ => nodeStr x depth)
                          sdd

            val next = helper depth succ

          in
              str
            @ [ curr
              ^ " -> "
              ^ (case vl of

                  SDD.Values v =>
                    next ^ " [label=\"" ^ (Values.toString v) ^ "\"];\n"

                | SDD.Nested n =>
                  let
                    val ghost  = "\"ghost"
                               ^ (Int.toString uid)
                               ^ "_"
                               ^ (Int.toString(SDD.uid n))
                               ^ "_"
                               ^ (Int.toString(SDD.uid succ))
                               ^ (depthStr depth)
                               ^ "\""
                    val nested = helper (depth +1) n
                  in
                    ghost ^ " [arrowhead=none];\n"
                  ^ ghost ^ " -> " ^ next   ^ ";\n"
                  ^ ghost ^ " -> " ^ nested ^ " [style=dashed,weight=0];\n"
                  ^ ghost ^ " [shape=point,label=\"\",height=0,width=0];\n"
                  end
                )
              ]
          end
          )
          []
          alpha
  end

  fun dotArcHelper () =
    HT.foldi (fn (sdd, ref depths, str) =>
               str @ (foldl (fn (d,str) =>
                              str @ (visitArc (fn () => [])
                                              (fn () => [])
                                              (nodeArc d)
                                              sdd
                                    )
                             )
                             []
                             depths
                     )
             )
             []
             nodes

  val l = ["digraph sdd {\n"]
          @
          (
          if x = SDD.one then
            [terminal 1 0]
          else if x = SDD.zero then
            [terminal 0 0]
          else
              (dotHelper x 0)
            @ (dotArcHelper ())
            @ (if maxShare then
                [terminal 1 0]
              else
                List.tabulate ( !maxDepth + 1, terminal 1)
              )
          )
          @ ["\n}"]
in
  String.concat l
end (* fun toDotHelper *)

(*--------------------------------------------------------------------------*)
fun toDot mode x =
  if nbNodes mode x > (LargeInt.fromInt 1000) then
    "digraph sdd {\n\n node \"42\" "
  ^ "[shape=rectangle,regular=true,label=\"Too much nodes (>1000)\"];\n"
  ^ "}\n"
  else
    toDotHelper mode x

(*--------------------------------------------------------------------------*)
fun homToDot h =
let

  fun helper h =
  let

    val node = "\"" ^ (Int.toString (Hom.uid h)) ^ "\""
    fun uid g = "\"" ^ (Int.toString (Hom.uid g)) ^ "\""

    fun id _ = node ^ " [label=\"ID\"];\n"

    fun cons vr vl nxt = "\n"

    fun const s = "\n"

    fun union hs =
      node ^ " [label=\"+\"];\n"
    ^ (foldl (fn (h,str) =>
               str ^ node ^ " -> " ^ (uid h) ^ ";\n"
             )
             ""
             hs
      )
    ^ (foldl (fn (h,str) => str ^ (helper h)) "" hs)

    fun inter hs =
      node ^ " [label=\"^\"];\n"
    ^ (foldl (fn (h,str) =>
               str ^ node ^ " -> " ^ (uid h) ^ ";\n"
             )
             ""
             hs
      )
    ^(foldl (fn (h,str) => str ^ (helper h)) "" hs)

    fun comp f g =
      node ^ " [label=\"o\"];\n"
    ^ node ^ " -> " ^ (uid f) ^ " [label=\"left\"];\n"
    ^ node ^ " -> " ^ (uid g) ^ " [label=\"right\"];\n"
    ^ (helper f)
    ^ (helper g)

    fun comcomp hs =
      node ^ " [label=\"@\"];\n"
    ^ (foldl (fn (h,str) =>
               str ^ node ^ " -> " ^ (uid h) ^ ";\n"
             )
             ""
             hs
      )
    ^ (foldl (fn (h,str) => str ^ (helper h)) "" hs)

    fun fixpoint h =
      node ^ " [label=\"*\"];\n"
    ^ node ^ " -> " ^ (uid h) ^ ";\n"
    ^ (helper h)

    fun nested h v =
      node ^ " [label=\"Nested(" ^ (Variable.toString v) ^ ")\"];\n"
    ^ node ^ " -> " ^ (uid h) ^ ";\n"
    ^ (helper h)

    fun func f v =
    let
      fun funcString (ref f) =
        case f Hom.Print of
          Hom.PrintRes s => s
        | _              => raise Hom.NotUserString
    in
      node ^ " [label=\"Func(" ^ (funcString f) ^ ","
    ^ (Variable.toString v) ^ ")\"];\n"
    end

    val visitor = Hom.mkVisitor ()
    val visit = visitor id cons const union inter comp comcomp fixpoint
                        nested func
  in
    visit h
  end

in
  "digraph hom {\n\n"
^ (helper h)
^ "}\n"
end

(*--------------------------------------------------------------------------*)
end (* fun ToolsFun *)
