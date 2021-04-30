#! /bin/bash
# HOW TO USE THIS SCRIPT?
#
# Run the following command: source get-cvc4-linux.sh from your bash prompt.
#
# This will download cvc4 version 1.8 and add it to your path
#

wget https://github.com/CVC4/CVC4/releases/download/1.8/cvc4-1.8-x86_64-linux-opt
mv cvc4-1.8-x86_64-linux-opt cvc4
chmod 755 cvc4

# rename folder to a generic name to make it easier to upgrade z3 versions
export PATH=$PATH:$PWD

