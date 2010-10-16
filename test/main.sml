SMLUnit.TextUITestRunner.runTest { output = TextIO.stdOut }
                                 ( TestSDD.suite() );

SMLUnit.TextUITestRunner.runTest { output = TextIO.stdOut }
                                 ( TestHom.suite() );
testDot();
