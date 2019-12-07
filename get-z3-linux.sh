#! /bin/bash

# HOW TO USE THIS SCRIPT?
#
# Run the following command: source get-z3-linux.sh from your bash prompt.
#
# This will download z3-4.8.6 and install z3 4.8.6.
#
# Subsequently, source the setup-z3-linux.sh script to bring Z3 into your
# path.  This latter step will have to be done repeatedly. (Or you can
# include it in your bashrc.)

wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.6/z3-4.8.6-x64-ubuntu-16.04.zip
unzip z3-4.8.6-x64-ubuntu-16.04.zip
cp z3-4.8.6-x64-ubuntu-16.04/bin/com.microsoft.z3.jar lib/

source setup-z3-linux.sh
