#!/bin/bash

echo "Moving into TrustedAbstractPlatform directory"
cd TrustedAbstractPlatform

echo "Generating TAP models ..."
cd modules
time make tap

echo "Running Proofs ..."
cd ../proofs
time make
