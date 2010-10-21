ML=mlton

TESTFLAGS= -const 'MLton.detectOverflow true'\
           -const 'Exn.keepHistory true'\
           -const 'MLton.safe true'

all:

check: ./test/main
	@(mkdir -p ./test/run && cd ./test/run && ../main)

./test/main:
	$(ML) $(TESTFLAGS) ./test/main.mlb

cleanTests:
	rm -f ./test/main
	rm -rf ./test/run

clean: cleanTests
