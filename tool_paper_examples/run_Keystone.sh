#!/bin/bash

echo "Moving into Keystone directory"
cd Keystone

echo "Generating TAP models"
cd modules
time make tap

echo "Running Proofs"
cd ../proofs
time make
