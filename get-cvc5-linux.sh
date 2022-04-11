#! /bin/bash
# HOW TO USE THIS SCRIPT?
#
# Run the following command: source get-cvc5-linux.sh from your bash prompt.
#
# This will download cvc5 version 0.0.4 and add it to your path
#

wget https://github.com/cvc5/cvc5/releases/download/cvc5-0.0.4/cvc5-Linux
mkdir -p cvc5/bin/
mv cvc5-Linux cvc5/bin/cvc5
chmod 755 cvc5/bin/cvc5
mv cvc5_wait.sh cvc5/bin/cvc5_wait.sh
export PATH=$PATH:$PWD/cvc5/bin
cvc5 --version

