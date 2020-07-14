#! /bin/bash

export PATH=$PATH:$PWD/z3/bin/
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$PWD/z3/bin/
sudo cp $PWD/z3/bin/libz3java.dylib /Library/Java/Extensions/
sudo cp $PWD/z3/bin/libz3.dylib /usr/local/lib/