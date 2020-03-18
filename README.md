<a href="https://travis-ci.org/uclid-org/uclid"><img src="https://travis-ci.org/uclid-org/uclid.svg?branch=master"></a>

# uclid5 Tutorial/Publication

The [tutorial](https://github.com/uclid-org/uclid/blob/master/tutorial/tutorial.pdf) has a gentle introduction to using uclid5.

If you use uclid5 in your work, please cite the following MEMOCODE 2018 paper:

Sanjit A. Seshia and Pramod Subramanyan. <font color="blue">UCLID5: Integrating Modeling, Verification, Synthesis and Learning.</font>
 [\[PDF\]](https://cse.iitk.ac.in/users/spramod/papers/memocode18.pdf)    
*Proceedings of the 16th ACM-IEEE International Conference on Formal Methods and Models for System Design*. **(MEMOCODE 2018)**. Beijing, China. October 2018.   

# Installation

## Pre-requisites

You will need the [Z3 SMT solver](https://github.com/Z3Prover/z3) to be installed on your system. If you are building Z3 from source, make sure the Z3/Java interface is enabled in your build (typically by passing `--java` to the `mk_make.py` script). 

uclid5 requires that the Z3 dynamic link library (libz3.so on Unix-like platforms) as well as the dynamic link library for the Z3/Java API (libz3java.so on Unix-like platforms) be in your dynamic library path (`$LD_LIBRARY_PATH` on Unix-like platforms; just `PATH` on Windows).


### Mac OS X El Capitan or up
System Integrity Protection is a feature introduced by Apple in OS X El Capitan; it prevents the modifications of system-owned files and directories by any process without a specific ‘entitlement’, even when executed by a root user or a user with root privileges. Since Java is a SIP protected executable, it ignores the user set DYLD_LIBRARY_PATH, which prevents the system from recognizing the Z3 Dynamic Library. 

To fix this issue, put:
- JNI dynamic link libraries (e.g libz3java.dylib) in:       /Library/Java/Extensions
- non-JNI dynamic link libraries (e.g libz3.dylib) in:      /usr/local/lib

For more information on the resolution of this issue, please refer to:
https://github.com/Z3Prover/z3/issues/294


## Download Pre-Built Binaries

Download the latest stable pre-built package from [releases tab](https://github.com/uclid-org/uclid/releases).

## Install From Source

Or, you could clone this repository and build from source. If you run into problems here, don't forget you can always fall back on the pre-built binaries linked above.


### Prerequisites

#### OpenJDK version 8 or Oracle JDK version 8

#### SBT version 1.0 or greater. 

Install instructions for sbt are available at http://www.scala-sbt.org/1.0/docs/Setup.html

#### Z3 version 4.6.0. 
Make sure the Z3/Java interface is enabled in your build (typically by passing `--java` to the `mk_make.py` script). 

uclid5 requires that the Z3 dynamic link library (libz3.so on Unix-like platforms) as well as the dynamic link library for the Z3/Java API (libz3java.so on Unix-like platforms) be in your dynamic library path (`$LD_LIBRARY_PATH` on Unix-like platforms; just `PATH` on Windows).

Finally copy the jar file  `path/to/z3/build/com.microsoft.z3.jar` to the dir `path/to/uclid5/lib/com.microsoft.z3.jar`


### Compiling uclid5

Ensure you have Z3 and sbt v1.0 or greater installed. Install instructions for sbt are available at http://www.scala-sbt.org/1.0/docs/Setup.html.

If all goes well, running update, clean, compile and test in sbt from the uclid5 directory should do the trick. The command to do all this is:

    $ sbt update clean compile "set fork:=true" test

If compilation and tests pass, you can build a universal package.

    $ sbt universal:packageBin

This will create uclid/target/universal/uclid-0.8.zip, which contains the uclid binary in the bin/ subdirectory. Unzip this file, and add it to your path.

## Installing and Running uclid5

    $ unzip uclid-0.9.5.zip
    $ cd uclid-0.9.5
    $ export PATH=$PATH:$PWD/bin

Now you can run uclid using the 'uclid' command. For example:

    $ uclid examples/tutorial/ex1.1-fib-model.ucl

# Directory Structure

This repository consists of the following sub-directories.
 - examples : This contains example uclid5 models. See examples/tutorial for the examples from the tutorial.
 - lib: Libraries on which uclid5 depends (Z3).
 - project: Build scripts.
 - src/main/scala: uclid5 source.
 - src/test/scala: uclid5 test suite.
 - test: test programs for uclid5.
 - tutorial: uclid5 tutorial (with LaTeX source)
 - vim: vim syntax highlighting for uclid5. 

# Related Tools

* [chiselucl](https://github.com/uclid-org/chiselucl) allows Chisel models to be converted into UCLID5.
