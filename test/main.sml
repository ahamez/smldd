print "\nTest SDD\n";
SMLUnit.TextUITestRunner.runTest { output = TextIO.stdOut }
                                 ( TestSDD.suite() );

print "\nTest Hom\n";
SMLUnit.TextUITestRunner.runTest { output = TextIO.stdOut }
                                 ( TestHom.suite() );

print "\nTest Util\n";
SMLUnit.TextUITestRunner.runTest { output = TextIO.stdOut }
                                 ( TestUtil.suite() );

print "\nTest Tools\n";
SMLUnit.TextUITestRunner.runTest { output = TextIO.stdOut }
                                 ( TestTools.suite() );

testDot();

print "\n";
