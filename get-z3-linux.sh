#! /bin/bash

VERSION=4.8.8

# HOW TO USE THIS SCRIPT?
#
# Run the following command: source get-z3-linux.sh from your bash prompt.
#
# This will download z3-$VERSION and install z3 $VERSION.
#
# Subsequently, source the setup-z3-linux.sh script to bring Z3 into your
# path.  This latter step will have to be done repeatedly. (Or you can
# include it in your bashrc.)

wget https://github.com/Z3Prover/z3/releases/download/z3-$VERSION/z3-$VERSION-x64-ubuntu-16.04.zip
unzip z3-$VERSION-x64-ubuntu-16.04.zip

# rename folder to a generic name to make it easier to upgrade z3 versions
rm -rf z3/
mv z3-$VERSION-x64-ubuntu-16.04/ z3/

cp z3/bin/com.microsoft.z3.jar lib/
source setup-z3-linux.sh
