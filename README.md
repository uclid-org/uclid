<a href="https://travis-ci.org/uclid-org/uclid"><img src="https://travis-ci.org/uclid-org/uclid.svg?branch=master"></a>

# Uclid Tutorial

See the [tutorial](https://github.com/uclid-org/uclid/blob/master/tutorial/tutorial.pdf).

# Pre-requisites

You will need the [Z3 SMT solver](https://github.com/Z3Prover/z3) to be installed on your system. If you are building Z3 from source, make sure the Z3/Java interface is enabled in your build (typically by passing `--java` to the `mk_make.py` script). 

Uclid requires that the Z3 dynamic link library (libz3.so on Unix-like platforms) as well as the dynamic link library for the Z3/Java API (libz3java.so on Unix-like platforms) be in your dynamic library path (`$LD_LIBRARY_PATH` on Unix-like platforms; just `PATH` on Windows).

# Compiling Uclid

Ensure you have Z3 and sbt v1.0 or greater installed. Install instructions for sbt are available at http://www.scala-sbt.org/1.0/docs/Setup.html.

If all goes well, running update, clean, compile and test in sbt should all work. The command to do all this is:

    $ sbt update clean compile test

#Installing Uclid

If compilation and tests pass, you can build a universal package.

    $ sbt universal:packageBin

This will create uclid/target/universal/uclid-0.8.zip, which contains the uclid binary in the bin/ subdirectory. Unzip this file, and add it to your path.

    $ cd target/universal/
    $ unzip uclid-0.8.zip
    $ cd uclid-0.8
    $ export PATH=$PATH:$PWD/bin

Now you can run uclid using the 'uclid' command. For example:

    $ uclid examples/tutorial/ex1.1-fib-model.ucl4

