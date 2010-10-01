fun main () =
  let
    (*val zero = SDD.zero*)
    (*val v0 = Vector.fromList [0];

    val v1  = Vector.fromList [1,2];
    val uv1 = ValuationUT.unify v1;

    val v2 = Vector.fromList [1,2];
    val uv2 = ValuationUT.unify v2;

    val v3 = Vector.fromList [~1,0,1,2,42];
    val uv3 = ValuationUT.unify v3;

    val v4= valuation_discrete_int.union (v2,v3)
    val v5 = valuation_discrete_int.intersection(v3,v1)
    val v6 = valuation_discrete_int.intersection(v0,v1)
    val v7 = valuation_discrete_int.difference(v2,v0)
    val v8 = valuation_discrete_int.difference(v3,v2)
    val v9 = valuation_discrete_int.difference(v8,v0)

    val l0 = [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,(Vector.fromList [101])]
    val o0 = (Union l0);
    val v10 = (Valuation_Operation.apply o0)*)

    (*val v0 = Vector.fromList [0,1,2,3]
    val v1 = Vector.fromList [0,45,2,~8773]
    val v2 = Vector.fromList [0,45,2,45,2,~1,0]

val _ = print(valuation_discrete_int.toString(valuation_discrete_int.sort v0))
val _ = print(valuation_discrete_int.toString(valuation_discrete_int.sort v1))
val _ = print(valuation_discrete_int.toString(valuation_discrete_int.sort v2))
*)

    val zero = SDD.zero
    val zer1 = SDD.zero
    val one  = SDD.one

    val s0 = SDD.flatNode(1,IntVector.fromList[1,2,0],one)
    val s1 = SDD.flatNode(1,IntVector.fromList[1,2,3],one)
    val s2 = SDD.flatNode(1,IntVector.fromList[42,100],one)

    val u0 = SDD.union [s0,s1,s2]

    val s3 = SDD.flatNode(2,IntVector.fromList[1],s0)
    val s4 = SDD.flatNode(2,IntVector.fromList[1],u0)
    val s5 = SDD.flatNode(2,IntVector.fromList[0],s1)
    val s6 = SDD.flatNode(2,IntVector.fromList[9],s0)

    val u1 = SDD.union [s3,s6]
    (*val u2 = SDD.union [s2,s4]*)
    (*val s2 = SDD.node(0,s1,one)*)
    (*val s3 = SDD.node(1,s1,s2)*)

    (*val u0 = SDD.union [one,one]*)
    (*val u1 = SDD.union [one,one]*)

    val i0 = SDD.intersection [zero,s0,s1,s2]
    val i1 = SDD.intersection [s0,s1]
    (*val i2 = SDD.intersection [s0,s2]*)
  in
    print "\nBEGIN TEST\n";
    (*print (Bool.toString(uv1 = uv2));
    print "\n";
    print (Bool.toString(uv1 = uv3));
    print "\n v4 ";
    print (valuation_discrete_int.toString v4);
    print "\n v5 ";
    print (valuation_discrete_int.toString v5);
    print "\n v6 ";
    print (valuation_discrete_int.toString v6);
    print "\n v7 ";
    print (valuation_discrete_int.toString v7);
    print "\n v8 ";
    print (valuation_discrete_int.toString v8);
    print "\n v9 ";
    print (valuation_discrete_int.toString v9);
    print "\n v10 ";
    print (valuation_discrete_int.toString v10);*)
    (*print "\n";
    print (Word32.toString (SDD.hash (!s1)));
    print "\n";
    print (Word32.toString (SDD.hash (!s4)));*)
    (*print "\n";*)
    (*print (Word32.toString (SDD.hash one));*)
    (*print "\n";
    print (Bool.toString (zero = one));
    print "\n";
    print (Bool.toString (zero = zer1));
    print "\n";
    print (Bool.toString (s1 = s0));
    print "\n";*)
    (*print "\n s0 = s0 ";
    print (Bool.toString (s0 = s0));
    print "\n s0 = s0bis ";
    print (Bool.toString (s0 = s0bis));
    print "\n s1 = s4 ";
    print (Bool.toString (s1 = s4));*)
    (*print "\n";
    print (Int.toString (SDD.paths one));
    print "\n";
    print (Int.toString (SDD.paths s0));
    print "\n";
    print (Int.toString (SDD.paths s1));
    print "\n";
    print (Int.toString (SDD.paths s2));
    print "\n";
    print (Int.toString (SDD.paths s3));
    print "\n";
    print (SDD.toString zero);
    print "\n";
    print (SDD.toString one);*)
    print "\n";
    print (SDD.toString u0);
    print "\n";
    print (SDD.toString u1);

    print "\n";
    print (SDD.toString i0);
    print "\n";
    print (SDD.toString i1);
    (*print "\n";
    print (SDD.toString i2);*)


    (*print "\n";
    print (SDD.toString u2);*)

    (*print "\n";
    print (SDD.toString s4);*)
    (*print "\n";*)
    (*print (Bool.toString (u0 = u1));*)
    print "\nEND TEST\n"
  end;

main ();
