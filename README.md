<a href="https://travis-ci.org/uclid-org/uclid"><img src="https://travis-ci.org/uclid-org/uclid.svg?branch=master"></a>

# Uclid Tutorial

See the [tutorial](https://github.com/uclid-org/uclid/blob/master/tutorial/tutorial.pdf). It also has installation instructions.

# Compiling and Installing Uclid

Ensure you have sbt v1.0 or greater installed. Install instructions 
for sbt are available at http://www.scala-sbt.org/1.0/docs/Setup.html.

If all goes well, running update, clean, compile and test in sbt should 
all work. The command to do all this is:

    $ sbt update clean compile test

If compilation and tests pass, you can build a universal package.

    $ sbt universal:packageBin

This will create uclid/target/universal/uclid-0.7.zip, which contains the uclid
binary in the bin/ subdirectory. Unzip this file, and add it to your path.

    $ cd target/universal/
    $ unzip uclid-0.7.zip
    $ cd uclid-0.7
    $ export PATH=$PATH:$PWD/bin
    $ cd ../../..

Now you can run uclid using the 'uclid' command. For example:

    $ uclid examples/tutorial/ex1.1-fib-model.ucl4

