#!/bin/bash

echo "Moving into Fib directory"
cd Fib

echo "Running uclid on fib.ucl ..."

echo "uclid -y \"cvc4 --lang=sygus2\" fib.ucl"
time uclid -y "cvc4 --lang=sygus2" fib.ucl
