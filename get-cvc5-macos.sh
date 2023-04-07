#! /bin/bash
# HOW TO USE THIS SCRIPT?
#
# Run the following command: source get-cvc5-macos.sh from your bash prompt.
#
# This will download cvc5 version 0.0.4 and add it to your path
#

mac_arch=$(uname -m)

if [ "$mac_arch" = "arm64" ]; then
    FILE_TO_GET="cvc5-macOS-arm64"
else
    FILE_TO_GET="cvc5-macOS"
fi

echo $FILE_TO_GET

wget https://github.com/cvc5/cvc5/releases/download/cvc5-1.0.3/$FILE_TO_GET

mkdir -p cvc5/bin/
mv $FILE_TO_GET cvc5/bin/cvc5
chmod 755 cvc5/bin/cvc5
mv cvc5_wait.sh cvc5/bin/cvc5_wait.sh
export PATH=$PATH:$PWD/cvc5/bin
cvc5 --version
