<a href="https://travis-ci.org/uclid-org/uclid"><img src="https://travis-ci.org/uclid-org/uclid.svg?branch=master"></a>

# uclid5 Tutorial

The [tutorial](https://github.com/uclid-org/uclid/blob/master/tutorial/tutorial.pdf) has a gentle introduction to using uclid5.

# Pre-requisites

You will need the [Z3 SMT solver](https://github.com/Z3Prover/z3) to be installed on your system. If you are building Z3 from source, make sure the Z3/Java interface is enabled in your build (typically by passing `--java` to the `mk_make.py` script). 

uclid5 requires that the Z3 dynamic link library (libz3.so on Unix-like platforms) as well as the dynamic link library for the Z3/Java API (libz3java.so on Unix-like platforms) be in your dynamic library path (`$LD_LIBRARY_PATH` on Unix-like platforms; just `PATH` on Windows).

# Download

Download the latest stable pre-built package from [releases tab](https://github.com/uclid-org/uclid/releases).

# Install From Source

Or, you could clone this repository and build from source. If you run into problems here, don't forget you can always fall back on the pre-built binaries linked above.

## Compiling uclid5

Ensure you have Z3 and sbt v1.0 or greater installed. Install instructions for sbt are available at http://www.scala-sbt.org/1.0/docs/Setup.html.

If all goes well, running update, clean, compile and test in sbt from the uclid5 directory should do the trick. The command to do all this is:

    $ sbt update clean compile test

## Installing uclid5

If compilation and tests pass, you can build a universal package.

    $ sbt universal:packageBin

This will create uclid/target/universal/uclid-0.8.zip, which contains the uclid binary in the bin/ subdirectory. Unzip this file, and add it to your path.

    $ cd target/universal/
    $ unzip uclid-0.8.zip
    $ cd uclid-0.8
    $ export PATH=$PATH:$PWD/bin

Now you can run uclid using the 'uclid' command. For example:

    $ uclid examples/tutorial/ex1.1-fib-model.ucl

## Directory Structure

This repository consists of the following sub-directories.
 - examples : This contains example uclid5 models. See examples/tutorial for the examples from the tutorial.
 - lib: Libraries on which uclid5 depends (Z3).
 - project: Build scripts.
 - src/main/scala: uclid5 source.
 - src/test/scala: uclid5 test suite.
 - test: test programs for uclid5.
 - tutorial: uclid5 tutorial (with LaTeX source)
 - vim: vim syntax highlighting for uclid5. 
