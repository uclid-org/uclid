#!/bin/bash

# Download and setup Z3.
./get-z3-linux.sh
./setup-z3-linux.sh

# Build UCLID5.
sbt compile
sbt universal:packageBin
cd target/universal/
unzip uclid-0.9.5.zip

# Add UCLID5 to PATH
export PATH="$(pwd)/uclid-0.9.5/bin:$PATH"