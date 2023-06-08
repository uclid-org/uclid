#! /bin/bash

sbt universal:packageBin
cd target/universal
rm -r uclid-0.9.5
unzip uclid-0.9.5.zip
cd uclid-0.9.5
export PATH=$PATH:$PWD/bin
cd ../../..
