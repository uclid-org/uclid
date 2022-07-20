<a href="https://travis-ci.org/uclid-org/uclid"><img src="https://travis-ci.org/uclid-org/uclid.svg?branch=master"></a>
![](https://github.com/uclid-org/uclid/workflows/Uclid%20CI/badge.svg)

# About

UCLID5 is an integrated modeling, verification and synthesis tool. UCLID5 is an evolution of the earlier UCLID modeling and verification system. The UCLID project was one of the first to develop satisfiability modulo theories (SMT) solvers and SMT-based verification methods. Here is the original UCLID paper that appeared at CAV 2002:

Randal E. Bryant, Shuvendu K. Lahiri, and Sanjit A. Seshia. <font color="blue">Modeling and Verifying Systems using a Logic of Counter Arithmetic with Lambda Expressions and Uninterpreted Functions.</font> [\[HTML\]](https://people.eecs.berkeley.edu/~sseshia/pubs/b2hd-bryant-cav02.html)
*Proceedings of the 14th International Conference on Computer-Aided Verification (CAV)*, pp. 78–92, LNCS 2404 , July 2002.

If you use UCLID5 in your work, please cite the following MEMOCODE 2018 paper:

Sanjit A. Seshia and Pramod Subramanyan. <font color="blue">UCLID5: Integrating Modeling, Verification, Synthesis and Learning.</font> [\[HTML\]](https://people.eecs.berkeley.edu/~sseshia/pubs/b2hd-seshia-memocode18.html)
*Proceedings of the 16th ACM-IEEE International Conference on Formal Methods and Models for System Design (MEMOCODE 2018)*, Beijing, China. October 2018.

For questions and feeback please contact elizabeth.polgreen [at] ed.ac.uk.


## Contact us

For bug reports, first preference is for you to file a GitHub issue. For help using UCLID5 in your work, please email uclid@lists.eecs.berkeley.edu



## UCLID5 Tutorial/Publication

The [tutorial](https://github.com/uclid-org/uclid/blob/master/tutorial/tutorial.pdf) has a gentle introduction to using UCLID5.


## Versions

Get the [latest release](https://github.com/uclid-org/uclid/releases), or get the latest development version `git clone https://github.com/uclid-ord/uclid`.

# Installation

## Prerequisites:
To use the prebuilt binaries, UCLID5 requires:
- [Z3 version 4.8.8.](https://github.com/Z3Prover/z3/releases/tag/z3-4.8.8) with the Java bindings
- [OpenJDK](https://openjdk.java.net/) version 8,9,10 or 11

To compile from source, UCLID5 requires all of the above plus:
- [SBT version 1.0 or greater.](https://www.scala-sbt.org/download.html)

The following are optional requirements but several CI tests will fail without them:
- (optional) [CVC5](https://github.com/cvc5/cvc5) version 0.0.4 is the SyGuS-IF compliant solver used for synthesis tests in the CI.
- (optional) [Delphi](https://github.com/polgreen/delphi) is used for verification modulo oracles tests in the CI.


## Installation of prerequisites on Linux
- For easy install of prerequisites on Linux, run the following scripts from the root directory of the UCLID5 source repository. These scripts set up Z3/CVC5/Delphi for use with uclid5. This script will download [Z3 version 4.8.8.](https://github.com/Z3Prover/z3/releases/tag/z3-4.8.8)/[CVC5 0.0.4](https://github.com/cvc5/cvc5/releases/tag/cvc5-0.0.4)/[Delphi](https://github.com/polgreen/delphi/releases/tag/0.1) binaries from GitHub.
~~~
    $ source get-z3-linux.sh
    $ source get-cvc5-linux.sh
    $ source get-delphi-linux.sh
~~~
- These scripts download the binaries for Z3, CVC5 and Delphi respectively and set up your `PATH` and `LD_LIBRARY_PATH` accordingly.
You may wish to permanently add the following lines to your bash_profile:
~~~
    export PATH=$PATH:/path/to/uclid/z3/bin:/path/to/uclid/cvc5/bin:/path/to/uclid/delphi/bin:/path/to/uclid/oracles
    export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/path/to/uclid/z3/bin
~~~

Alternatively, [Z3](https://github.com/Z3Prover/z3), [CVC5](https://github.com/cvc5/cvc5), and [Delphi](https://github.com/polgreen/delphi) can all be built from source, and instructions can be found on their respective git repositories. If you prefer to build Z3 from source, make sure the Z3/Java interface is enabled in your build (currently by passing `--java` to the `mk_make.py` script).

- Install instructions for SBT are available at http://www.scala-sbt.org/1.0/docs/Setup.html
- Install instructions for OpenJDK are available at https://openjdk.java.net/install/

## Installation of prerequisites on MacOS
- For easy install of prerequisites on macOS, run the following scripts from the root directory of the UCLID5 source repository. These scripts set up Z3/CVC5/Delphi for use with uclid5. This script will download [Z3 version 4.8.8.](https://github.com/Z3Prover/z3/releases/tag/z3-4.8.8)/[CVC5 0.0.4](https://github.com/cvc5/cvc5/releases/tag/cvc5-0.0.4)/[Delphi](https://github.com/polgreen/delphi/releases/tag/0.1) binaries from GitHub.
~~~
    $ source get-z3-macos.sh
    $ source get-cvc5-macos.sh
    $ source get-delphi-macos.sh
~~~
- These scripts add the downloaded binaries to your `PATH` and `LD_LIBRARY_PATH` accordingly. You may wish to permanently add the following lines to your bash_profile:
~~~
    export PATH=$PATH:/path/to/uclid/z3/bin:/path/to/uclid/cvc5/bin:/path/to/uclid/delphi/bin:/path/to/uclid/oracles
~~~
- Due to System Integrity Protection, introduced in OS X El Capitan, Java ignores the user set DYLD_LIBRARY_PATH. To fix this issue copy the JNI dynamic link libraries to Java/Library/Extensions and the non-JNI dynamic link libraries to /usr/local/lib as follows (if you build Z3 from source these files are found in the build directory):
~~~
    cp /path/to/uclid/z3/bin/libz3.dylib /usr/local/lib
    cp /path/to/uclid/z3/bin/libz3java.dylib /Library/Java/Extensions
~~~

- To install SBT run `brew install sbt`
- To install openJDK run `brew install openjdk@11`. If this does not work, you may need to run
- Make sure Java 11 is the default by adding the following lines to your dotfiles. For `bash` this is usually `.bash_profile` and for `zsh` this is usually `.zshrc`.
```
export JAVA_11_HOME=$(/usr/libexec/java_home -v11)
alias java11='export JAVA_HOME=$JAVA_11_HOME'
java11
```

## Compiling uclid5

Run the following command in the root directory of the UCLID5 repository (note that it is not necessary to run `sbt update` if you already have the correct dependencies installed as per https://github.com/uclid-org/uclid/blob/master/build.sbt. However, running it will do no harm.):

    $ sbt update clean compile "set fork:=true" test

If compilation and tests pass (or if the only failing tests are due to CVC5 and Delphi not being found), you can build a universal package.

    $ sbt universal:packageBin

This will create uclid/target/universal/uclid-0.9.5.zip, which contains the uclid binary in the bin/ subdirectory. Unzip this file, and add it to your path.

    $ unzip uclid-0.9.5.zip
    $ cd uclid-0.9.5
    $ export PATH=$PATH:$PWD/bin

## Running UCLID

Now you can run uclid using the 'uclid' command. For example:

    $ uclid examples/tutorial/ex1.1-fib-model.ucl

 Some useful commands to know:
 - To print the SMT files use the `-g` flag, e.g., `uclid examples/tutorial/ex1.1-fib-model.ucl -g "filename"` will print the SMT file to SMT files with the prefix `filename`.
 - To run UCLID5 with another solver use the `-s` flag, e.g., `uclid examples/tutorial/ex1.1-fib-model.ucl -s "cvc5 --lang smt2 --produce-models"` will use CVC5 as the back-end solver.

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
