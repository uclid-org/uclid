#! /bin/bash

wget https://github.com/polgreen/delphi/releases/download/0.1/delphi_linux

mkdir -p delphi/bin/
mv delphi_linux delphi/bin/delphi

chmod 755 delphi/bin/delphi
export PATH=$PATH:$PWD/delphi/bin

