ML=mlton

TESTFLAGS= -const 'MLton.detectOverflow true'\
           -const 'Exn.keepHistory true'\
           -const 'MLton.safe true'

SOURCES=./smldd/sources.mlb                                  \
        ./smldd/Util.sml                                     \
        ./smldd/exceptions.sml                               \
        ./smldd/Hash.sml                                     \
        ./smldd/storage/signatures/DATA.sml                  \
        ./smldd/storage/signatures/OPERATION.sml             \
        ./smldd/storage/Cache.sml                            \
        ./smldd/storage/UnicityTable.sml                     \
        ./smldd/BitWord.sml                                  \
        ./smldd/IntSortedVector.sml                          \
        ./smldd/parameters/signatures/IDENTIFIER.sml         \
        ./smldd/parameters/signatures/VALUES.sml             \
        ./smldd/parameters/signatures/VARIABLE.sml           \
        ./smldd/parameters/instances/BitWordValues.sml       \
        ./smldd/parameters/instances/DiscreteIntValues.sml   \
        ./smldd/parameters/instances/IntVariable.sml         \
        ./smldd/parameters/instances/StringIdentifier.sml    \
        ./smldd/squareUnion.sml                              \
        ./smldd/commonApply.sml                              \
        ./smldd/unionSDD.sml                                 \
        ./smldd/unionFlatDiscreteSDD.sml                     \
        ./smldd/SDD.sml                                      \
        ./smldd/Hom.sml                                      \
        ./smldd/Order.sml                                    \
        ./smldd/Tools.sml                                    \
        ./smldd/configurations.sml

TESTSOURCES=./test/main.mlb      \
            ./test/TestDot.sml   \
            ./test/TestHom.sml   \
            ./test/TestOrder.sml \
            ./test/TestSDD.sml   \
            ./test/TestUtil.sml  \
            ./test/main.sml


all:

check: ./test/main
	@(mkdir -p ./test/run && cd ./test/run && ../main)

./test/main: $(TESTSOURCES) $(SOURCES)
	$(ML) $(TESTFLAGS) ./test/main.mlb

cleanTests:
	rm -f ./test/main
	rm -rf ./test/run

clean: cleanTests
