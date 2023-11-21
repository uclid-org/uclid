#! /bin/bash

VERSION=4.12.2

# HOW TO USE THIS SCRIPT?
#
# Run the following command: source get-z3-linux.sh from your bash prompt.
#
# This will download z3-$VERSION and install z3 $VERSION.
#
# Subsequently, source the setup-z3-linux.sh script to bring Z3 into your
# path.  This latter step will have to be done repeatedly. (Or you can
# include it in your bashrc.)

mac_arch=$(uname -m)

if [ "$mac_arch" = "arm64" ]; then
    FILE_TO_GET="z3-$VERSION-arm64-osx-11.0"
else
    FILE_TO_GET="z3-$VERSION-x64-osx-10.16"
fi

echo $FILE_TO_GET

wget https://github.com/Z3Prover/z3/releases/download/z3-$VERSION/$FILE_TO_GET.zip
unzip $FILE_TO_GET.zip
rm $FILE_TO_GET.zip

# rename folder to a generic name to make it easier to upgrade z3 versions
rm -rf z3/
mv $FILE_TO_GET/ z3/

cp z3/bin/com.microsoft.z3.jar lib/
source setup-z3-macos.sh
