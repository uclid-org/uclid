#! /bin/bash
# HOW TO USE THIS SCRIPT?
#
# Run the following command: source get-cvc4-linux.sh from your bash prompt.
#
# This will download cvc4 version 1.8 and add it to your path
#

wget https://github.com/CVC4/CVC4/releases/download/1.8/cvc4-1.8-x86_64-linux-opt
mkdir -p cvc4/bin/
mv cvc4-1.8-x86_64-linux-opt cvc4/bin/cvc4
chmod 755 cvc4/bin/cvc4
export PATH=$PATH:$PWD/cvc4/bin
cvc4 --version

