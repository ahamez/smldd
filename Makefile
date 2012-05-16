ML=mlton

TESTFLAGS=-cc-opt -O0            \
          -drop-pass deepFlatten

PROFFLAGS=-cc-opt -O0          \
          -profile count       \
          -profile-branch true \

SOURCES=./smldd/sources.mlb                                  \
        ./smldd/Util.sml                                     \
        ./smldd/exceptions.sml                               \
        ./smldd/Hash.sml                                     \
        ./smldd/storage/signatures/DATA.sml                  \
        ./smldd/storage/signatures/OPERATION.sml             \
        ./smldd/storage/Cache.sml                            \
        ./smldd/storage/UnicityTable.sml                     \
        ./smldd/IntSortedVector.sml                          \
        ./smldd/parameters/signatures/VALUES.sml             \
        ./smldd/parameters/signatures/VARIABLE.sml           \
        ./smldd/parameters/instances/DiscreteIntValues.sml   \
        ./smldd/parameters/instances/IntVariable.sml         \
        ./smldd/squareUnion.sml                              \
        ./smldd/commonApply.sml                              \
        ./smldd/unionSDD.sml                                 \
        ./smldd/SDD.sml                                      \
        ./smldd/Hom.sml                                      \
        ./smldd/Tools.sml                                    \
        ./smldd/configurations.sml

TESTSOURCES=./test/main.mlb               \
            ./test/testConfigurations.sml \
            ./test/TestDot.sml            \
            ./test/TestHom.sml            \
            ./test/TestSDD.sml            \
            ./test/TestUtil.sml           \
            ./test/main.sml

all:

check: ./test/main
	@(mkdir -p ./test/run && cd ./test/run && ../main)

./test/main: $(TESTSOURCES) $(SOURCES)
	$(ML) $(TESTFLAGS) ./test/main.mlb

prof: ./test/main-prof
	@(mkdir -p ./test/run && cd ./test/run && ../main-prof)
	@./test/prof.sh

./test/main-prof: $(TESTSOURCES) $(SOURCES)
	$(ML) $(PROFFLAGS) -output ./test/main-prof ./test/main.mlb

cleanTests:
	rm -f ./test/main
	rm -f ./test/main-prof
	rm -rf ./test/run

clean: cleanTests
