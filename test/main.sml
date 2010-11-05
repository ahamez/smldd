SMLUnit.TextUITestRunner.runTest { output = TextIO.stdOut }
                                 ( TestSDD.suite() );

SMLUnit.TextUITestRunner.runTest { output = TextIO.stdOut }
                                 ( TestHom.suite() );

SMLUnit.TextUITestRunner.runTest { output = TextIO.stdOut }
                                 ( TestUtil.suite() );

SMLUnit.TextUITestRunner.runTest { output = TextIO.stdOut }
                                 ( TestOrder.suite() );

SMLUnit.TextUITestRunner.runTest { output = TextIO.stdOut }
                                 ( TestTools.suite() );

testDot();
