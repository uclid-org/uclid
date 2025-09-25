#! /bin/bash

wget https://github.com/polgreen/delphi/releases/download/0.2/delphi_mac

mkdir -p delphi/bin/
mv delphi_mac delphi/bin/delphi

chmod 755 delphi/bin/delphi
export PATH=$PATH:$PWD/delphi/bin

