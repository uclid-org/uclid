#!/bin/bash

echo "Moving into TrustedAbstractPlatform directory"
cd TrustedAbstractPlatform

echo "Verifying TAP model ..."
cd modules
time make tap

echo "Verify integrity proof ..."
cd ../proofs
time make

echo "Returning to examples directory ..."
cd ../../

echo "Cloning Boogie TAP models repo ..."
git clone git@github.com:0tcb/TAP.git

echo "Verifying TAP models in Boogie ..."
cd TAP/AbstractPlatform
time boogie CPU.bpl CPUImpl.bpl Types.bpl ../Common/Cache.bpl ../Common/CacheImpl.bpl ../Common/Common.bpl ../Common/Types.bpl

echo "Verifying integrity proof model in Boogie ..."
time boogie IntegrityProof.bpl CPU.bpl CPUImpl.bpl Types.bpl ../Common/Cache.bpl ../Common/CacheImpl.bpl ../Common/Common.bpl ../Common/Types.bpl ProofCommon.bpl /proc:ProveIntegrity
