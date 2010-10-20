(*--------------------------------------------------------------------------*)
signature TOOLS = sig

  type SDD
  val nbPaths       : SDD -> IntInf.int

  datatype mode  = Sharing | Hierarchy

  val toDot      : mode -> SDD -> string
end (* signature TOOLS *)

(*--------------------------------------------------------------------------*)
functor ToolsFun ( structure SDD : SDD
                   and Variable  : VARIABLE where type t      = SDD.variable
                   and Values    : VALUES   where type values = SDD.values
                 )
  : TOOLS
= struct

(*--------------------------------------------------------------------------*)
type SDD = SDD.SDD

(*--------------------------------------------------------------------------*)
datatype mode = Sharing | Hierarchy

(*--------------------------------------------------------------------------*)
structure HT = HashTable

(* Count the number of distinct paths in an SDD *)
fun nbPaths x =
let

  val visit = SDD.mkVisitor SDD.Cached

  fun zero () = IntInf.fromInt 0
  fun one  () = IntInf.fromInt 1

  fun node _ _ alpha =
    foldl (fn ( (vl,succ) , nb) =>
            case vl of
              SDD.Values v => nb +   (IntInf.fromInt (Values.length v))
                                   * visit zero one node succ
            | SDD.Nested n => nb +   visit zero one node n
                                   * visit zero one node succ
          )
          (IntInf.fromInt 0)
          alpha

in
  visit zero one node x
end (* fun visitNbPaths *)

(*--------------------------------------------------------------------------*)
(* Indicate if the dot output emphasizes on hierarchy or sharing *)
datatype dotMode = ShowSharing | ShowHierarchy

(*--------------------------------------------------------------------------*)
(* Export an SDD to a DOT representation *)


fun toDot mode x =
let

  val visit = SDD.mkVisitor SDD.NonCached

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

  (* Associate an SDD to a list of all hierarchies it belongs to *)
  val nodes : ( ( SDD , int list ref ) HT.hash_table )
        = (HT.mkTable( SDD.hash , op = ) ( 10000, DoNotPanic ))

  val maxDepth = ref 0

  fun dotHelper sdd depth =
  let
    val _ = case HT.find nodes sdd of
              NONE        => HT.insert nodes ( sdd, ref [depth] )
            | SOME depths =>
              if maxShare then
                (* Insert only for the first time, as in real sharing mode,
                   we don't care about depth *)
                ()
              else
              let
                fun insertSorted x [] = []
                |   insertSorted x (Y as (y::ys)) =
                  if x = y then
                    Y
                  else if x < y then
                    x::Y
                  else
                    y::(insertSorted x ys)
              in
                depths := insertSorted depth (!depths)
              end
    val _ = if depth > !maxDepth then
              maxDepth := depth
            else
              ()
  in
    visit (fn () => []) (fn () => []) (node depth dotHelper) sdd
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
            let
              fun workaround x _ _ = nodeStr x depth
            in
              visitString (fn () => raise DoNotPanic)
                          (fn () => "terminal1" ^ (depthStr depth))
                          workaround
                          sdd
            end

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
                              str @ (visit (fn () => [])
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

  val l = if x = SDD.one then
            [terminal 1 0]
          else if x = SDD.zero then
            [terminal 0 0]
          else
              ["digraph sdd {\n"]
            @ (dotHelper x 0)
            @ (dotArcHelper ())
            @ (if maxShare then
                [terminal 1 0]
              else
                List.tabulate ( !maxDepth + 1, terminal 1)
              )
            @ ["\n}"]
in
  String.concat l
end (* fun toDot *)

(*--------------------------------------------------------------------------*)
end (* fun ToolsFun *)
