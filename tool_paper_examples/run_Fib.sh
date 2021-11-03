#!/bin/bash

echo "Moving into Control directory"
cd Fib

echo "Running uclid on fib.ucl"

echo "uclidtool -y \"cvc4 --lang=sygus2\" fib.ucl"
time uclidtool -y "cvc4 --lang=sygus2" fib.ucl