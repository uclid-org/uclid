#!/bin/bash

echo "Moving into OperAxUhb directory"
cd OperAxUhb

echo "Running uclid on operAx.ucl ..."
echo 'uclid uhb_common.ucl operAx.ucl'
time uclid uhb_common.ucl operAx.ucl
