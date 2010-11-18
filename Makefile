ML=mlton

TESTFLAGS=

PROFFLAGS=-profile count       \
          -profile-branch true \

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

TESTSOURCES=./test/main.mlb               \
            ./test/testConfigurations.sml \
            ./test/TestDot.sml            \
            ./test/TestHom.sml            \
            ./test/TestOrder.sml          \
            ./test/TestSDD.sml            \
            ./test/TestUtil.sml           \
            ./test/TestTools.sml          \
            ./test/main.sml

all:

check: ./test/main
	@(mkdir -p ./test/run && cd ./test/run && ../main)

./test/main: $(TESTSOURCES) $(SOURCES)
	$(ML) $(TESTFLAGS) ./test/main.mlb

EXCLUDE="Assert Posix StreamIOExtra IEEEReal HashTable Date Primitive Real\
        Net OS Timer Word ImperativeIO Sequence Assert MLton Array \
        String Substring Socket TextUITestRunner Test \
        'Util.shuffle.<case NONE>' CacheFun UnicityTableFunID\
        'DiscreteIntValues.Operations.apply.<case Union \[\]>' BitWord\
				'squareUnion.mergeSuccs.insert.insertHelper.<case true>'\
				'squareUnion.mergeVls.insert.<case true>'\
				'HomFun.Evaluation.apply.<case Id>'\
				'HomFun.Evaluation.apply.<case Const _>'"
FILTER=$(shell for i in "$(EXCLUDE)" ; do echo ^$$i\|\\c ; done ; echo "^ ")

EXCLUDE2="String stats Dot"
FILTER2=$(shell for i in "$(EXCLUDE2)" ; do echo $$i\|\\c ; done ; echo "^ ")

prof: ./test/main-prof
	@(mkdir -p ./test/run && cd ./test/run && ../main-prof)
	mlprof -raw true -show-line true ./test/main-prof ./test/run/mlmon.out \
	| grep '(0)' | grep -v -E -e '$(FILTER)' | grep -v -E -e '$(FILTER2)'

./test/main-prof: $(TESTSOURCES) $(SOURCES)
	$(ML) $(TESTFLAGS) $(PROFFLAGS) -output ./test/main-prof ./test/main.mlb

cleanTests:
	rm -f ./test/main
	rm -f ./test/main-prof
	rm -rf ./test/run

clean: cleanTests
