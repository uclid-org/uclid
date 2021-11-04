#!/bin/bash

echo "Moving into TrainSystem"
cd TrainSystem

echo "Running uclid on TrainSystem.ucl ..."
echo 'uclid -s "z3 -in" TrainSystem.ucl'
time uclid -s "z3 -in" TrainSystem.ucl
