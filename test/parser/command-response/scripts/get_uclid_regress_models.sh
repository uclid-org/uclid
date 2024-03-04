#!/bin/bash

# Run this from the inside the `output` directory with the following command:
#   ../scripts/get_uclid_regress_models.sh

# Add the following lines under line 413 in SMTLIB2Interface.scala
# val file = new File(lang.NameProvider.get("parser_out").name)
# val bw = new BufferedWriter(new FileWriter(file))
# bw.write(str)
# bw.close()


echo "Generating UCLID SMT files ."

for f in ../../../*.ucl
do 
  uclid -s "z3 -in" $f
done

