#! /bin/bash

python3 parser.py
dir="./parser_test/*"
sbt universal:packageBin
cd target/universal
rm -rf uclid-0.9.5
unzip uclid-0.9.5.zip
cd uclid-0.9.5
export PATH=$PATH:$PWD/bin
cd ..
cd ..
cd ..
for file in $dir
do
  filename=$(basename "$file" .ucl)
  echo $'\n'
  echo uclid "parser_test/"$filename.ucl
  uclid "parser_test/"$filename.ucl
done
