print "\nTest SDD\n";
SMLUnit.TextUITestRunner.runTest { output = TextIO.stdOut }
                                 ( TestSDD.suite() );

print "\nTest Hom\n";
SMLUnit.TextUITestRunner.runTest { output = TextIO.stdOut }
                                 ( TestHom.suite() );

print "\nTest Util\n";
SMLUnit.TextUITestRunner.runTest { output = TextIO.stdOut }
                                 ( TestUtil.suite() );

print "\nTest Order\n";
SMLUnit.TextUITestRunner.runTest { output = TextIO.stdOut }
                                 ( TestOrder.suite() );

print "\nTest Tools\n";
SMLUnit.TextUITestRunner.runTest { output = TextIO.stdOut }
                                 ( TestTools.suite() );

print "\nTest BitWord\n";
SMLUnit.TextUITestRunner.runTest { output = TextIO.stdOut }
                                 ( TestBitWord.suite() );

print "\nTest Env\n";
SMLUnit.TextUITestRunner.runTest { output = TextIO.stdOut }
                                 ( TestEnv.suite() );


testDot();

print "\n";
