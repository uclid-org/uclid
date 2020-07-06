<a href="https://travis-ci.org/uclid-org/uclid"><img src="https://travis-ci.org/uclid-org/uclid.svg?branch=master"></a>
![](https://github.com/uclid-org/uclid/workflows/Uclid%20CI/badge.svg)

# uclid5 Tutorial/Publication

The [tutorial](https://github.com/uclid-org/uclid/blob/master/tutorial/tutorial.pdf) has a gentle introduction to using uclid5.

If you use uclid5 in your work, please cite the following MEMOCODE 2018 paper:

Sanjit A. Seshia and Pramod Subramanyan. <font color="blue">UCLID5: Integrating Modeling, Verification, Synthesis and Learning.</font>
 [\[PDF\]](https://cse.iitk.ac.in/users/spramod/papers/memocode18.pdf)    
*Proceedings of the 16th ACM-IEEE International Conference on Formal Methods and Models for System Design*. **(MEMOCODE 2018)**. Beijing, China. October 2018. 

# Installation
There are currently two ways to install UCLID5: downloading the latest pre-build package and building from source. Please make sure you have all the pre-requisites before proceeding to installation. Due to the nuances in the later Mac OS versions, we prepare separately a compact list of the installation instructions [here](mac-install.md). 

## Pre-requisites

#### 1. [Z3 version 4.6.0.](https://github.com/Z3Prover/z3/releases/tag/z3-4.6.0)
You will need the Z3 SMT solver to be installed on your system. If you are building Z3 from source, make sure the Z3/Java interface is enabled in your build (typically by passing `--java` to the `mk_make.py` script). To install z3 on Unix-like systems, download the source code and run the following:

```bash
python scripts/mk_make.py --java
cd build
make
sudo make install
```

uclid5 requires that the Z3 dynamic link library (libz3.so on Unix-like platforms) as well as the dynamic link library for the Z3/Java API (libz3java.so on Unix-like platforms) be in your dynamic library path (`$LD_LIBRARY_PATH` on Unix-like platforms; just `PATH` on Windows).

**If you are using Mac OS X El Capitan or above**, System Integrity Protection is a feature introduced by Apple in OS X El Capitan; it prevents the modifications of system-owned files and directories by any process without a specific ‘entitlement’, even when executed by a root user or a user with root privileges. Since Java is a SIP protected executable, it ignores the user set DYLD_LIBRARY_PATH, which prevents the system from recognizing the Z3 Dynamic Library. 

To fix this issue, put:
- JNI dynamic link libraries (e.g libz3java.dylib) in:       /Library/Java/Extensions
- non-JNI dynamic link libraries (e.g libz3.dylib) in:      /usr/local/lib

For more information on the resolution of this issue, please refer to:
https://github.com/Z3Prover/z3/issues/294

#### 2. [OpenJDK version 8](https://openjdk.java.net/) or [Oracle JDK version 8](https://www.oracle.com/java/technologies/javase/javase-jdk8-downloads.html)
**If you are using Mac OS X Mojave or above**, we recommend using Java 11 or earlier. We have found some issues related to the System Integrity Protection when using Catalina or Mojave and later versions of OpenJDK.

#### 3. [SBT version 1.0 or greater.](http://www.scala-sbt.org/1.0/docs/Setup.html)
If you intend to build from source, you need to install sbt. You can skip this step if you are using the pre-build binaries. Install instructions for sbt are available at http://www.scala-sbt.org/1.0/docs/Setup.html

## Download Pre-Built Binaries

Download the latest stable pre-built package from [releases tab](https://github.com/uclid-org/uclid/releases).

## Building From Source

Or, you could clone this repository and build from source. If you run into problems here, don't forget you can always fall back on the pre-built binaries linked above.


### Prerequisites
Before you begin, make sure you have the following installed and properly set up:

#### 1. Z3 version 4.6.0. 
Make sure the Z3/Java interface is enabled in your build (typically by passing `--java` to the `mk_make.py` script). 

**(Z3 configuration)** uclid5 requires that the Z3 dynamic link library (libz3.so on Unix-like platforms) as well as the dynamic link library for the Z3/Java API (libz3java.so on Unix-like platforms) be in your dynamic library path (`$LD_LIBRARY_PATH` on Unix-like platforms; just `PATH` on Windows).

Finally copy the jar file  `path/to/z3/build/com.microsoft.z3.jar` to the dir `path/to/uclid5/lib/com.microsoft.z3.jar`

#### 2. OpenJDK version 8 or Oracle JDK version 8

#### 3. SBT version 1.0 or greater. 

Install instructions for sbt are available at http://www.scala-sbt.org/1.0/docs/Setup.html


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
