#!/bin/bash

echo "Moving into TrainSystem"
cd TrainSystem

echo "Running uclid on TrainSystem.ucl ..."
echo 'uclid TrainSystem.ucl'
time uclid TrainSystem.ucl
