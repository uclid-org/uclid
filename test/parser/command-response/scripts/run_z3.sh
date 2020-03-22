#!/bin/bash
  
# Saves Z3 output for all .smt files in the test-files directory
# This also deletes the current files in output, so use carefully

# Run this from the top level directory `command-output`

echo "Generating Z3 output for test files."
rm output/*

for f in test-files/*.smt
do 
  touch ./output/$(basename $f .smt).out
  z3 -T:60 $f > ./output/$(basename $f .smt).out
done
