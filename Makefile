all:
	sbt compile
	sbt "run ./test/test7.ucl4"

build:
	sbt compile

run:
	sbt "run ./test/test1.ucl4"
	sbt "run ./test/test-types-0.ucl4"
	sbt "run ./test/test3.ucl4"
	sbt "run ./test/test4.ucl4"
	sbt "run ./test/test5.ucl4"
	sbt "run ./test/test6.ucl4"

specs:
	sbt "run ./test/spec1.ucl4"
	
test-int-fib: 
	sbt "run ./test/test-int-fib.ucl4"

test-bv-fib: 
	sbt "run -m test ./test/test-bv-fib.ucl4"

test-mc91: 
	sbt "run ./test/test-mc91.ucl4"

test-types-0: 
	sbt "run ./test/test-types-0.ucl4"

test-type1: 
	sbt "run -m test ./test/test-type1.ucl4"

test-tuple-record-1:
	sbt "run ./test/test-tuple-record-1.ucl4"

test-bv-assign:
	sbt "run ./test/test-bv-assign.ucl4"

test-forloop-0:
	sbt "run ./test/test-forloop-0.ucl4"

test-forloop-1:
	sbt "run ./test/test-forloop-1.ucl4"

test-forloop:
	sbt "run ./test/test-forloop.ucl4"

test-inliner:
	sbt "run ./test/test-inliner.ucl4"
	
.PHONY: all build run specs test-int-fib test-types-0 test-type1 test-bv-fib test-forloop test-forloop-0 test-forloop-1 test-bv-assign test-inliner
