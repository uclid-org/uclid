all:
	sbt compile
	sbt "run ./test/test7.ucl4"

build:
	sbt compile

run:
	sbt "run ./test/test1.ucl4"
	sbt "run ./test/test2.ucl4"
	sbt "run ./test/test3.ucl4"
	sbt "run ./test/test4.ucl4"
	sbt "run ./test/test5.ucl4"
	sbt "run ./test/test6.ucl4"

specs:
	sbt "run ./test/spec1.ucl4"
	
