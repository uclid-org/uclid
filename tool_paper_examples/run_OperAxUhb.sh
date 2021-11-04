#!/bin/bash

echo "Moving into OperAxUhb directory"
cd OperAxUhb

echo "Running uclid on operAx.ucl ..."
echo 'uclid -s "z3 -in" uhb_common.ucl operAx.ucl'
time uclid -s "z3 -in" uhb_common.ucl operAx.ucl