#!/bin/bash

#uclid5_tap_files="TrustedAbstractPlatform/modules/abstract-cache.ucl TrustedAbstractPlatform/modules/abstract-cpu.ucl TrustedAbstractPlatform/modules/ap-types.ucl TrustedAbstractPlatform/modules/common-types.ucl TrustedAbstractPlatform/modules/tap-mod.ucl"
uclid5_tap_files="TrustedAbstractPlatform/modules/ap-types.ucl TrustedAbstractPlatform/modules/common-types.ucl TrustedAbstractPlatform/modules/tap-mod.ucl"
boogie_tap_files="TAP/AbstractPlatform/CPU.bpl TAP/AbstractPlatform/CPUImpl.bpl TAP/AbstractPlatform/ImplCommon.bpl TAP/AbstractPlatform/Types.bpl"

uclid5_integrity_files="TrustedAbstractPlatform/proofs/proof-common.ucl TrustedAbstractPlatform/proofs/integrity-proof.ucl"
boogie_integrity_files="TAP/AbstractPlatform/ProofCommon.bpl TAP/AbstractPlatform/IntegrityProof.bpl"

# Count the TAP modules...
echo "Counting TAP module stats ============================================"
b=$boogie_tap_files
u=$uclid5_tap_files

# Count #fn
echo "Boogie #fn: $(grep -r "function" $b | wc -l)";
echo "UCLID5 #fn: $(grep -r "function" $u | wc -l)";

# Count #pr
echo "Boogie #pr: $(grep -r "procedure" $b | wc -l)"
echo "UCLID5 #pr: $(grep -r "procedure" $u | wc -l)"

# Count #an
boogie_reqcnt=$(grep -r "requires" $b | wc -l)
uclid5_reqcnt=$(grep -r "requires" $u | wc -l)
boogie_encnt=$(grep -r "ensures" $b | wc -l)
uclid5_encnt=$(grep -r "ensuress" $u | wc -l)
boogie_invcnt=$(grep -r "invariant" $b | wc -l)
uclid5_invcnt=$(grep -r "invariant" $u | wc -l)
echo "Boogie #an:       $(($boogie_reqcnt + $boogie_encnt + $boogie_invcnt))"
echo "UCLID5 #an:       $(($uclid5_reqcnt + $uclid5_encnt + $uclid5_invcnt))"

#Count #ln
echo "Boogie #ln: $(cat $b | wc -l)"
echo "UCLID5 #ln: $(cat $u | wc -l)"

# Count the TAP proof...
echo "Counting Integrity proof stats ============================================"
b=$boogie_integrity_files
u=$uclid5_integrity_files

# Count #fn
echo "Boogie #fn: $(grep -r "function" $b | wc -l)";
echo "UCLID5 #fn: $(grep -r "function" $u | wc -l)";

# Count #pr
echo "Boogie #pr: $(grep -r "procedure" $b | wc -l)"
echo "UCLID5 #pr: $(grep -r "procedure" $u | wc -l)"

# Count #an
boogie_reqcnt=$(grep -r "requires" $b | wc -l)
uclid5_reqcnt=$(grep -r "requires" $u | wc -l)
boogie_encnt=$(grep -r "ensures" $b | wc -l)
uclid5_encnt=$(grep -r "ensuress" $u | wc -l)
boogie_invcnt=$(grep -r "invariant" $b | wc -l)
uclid5_invcnt=$(grep -r "invariant" $u | wc -l)
echo "Boogie #an:       $(($boogie_reqcnt + $boogie_encnt + $boogie_invcnt))"
echo "UCLID5 #an:       $(($uclid5_reqcnt + $uclid5_encnt + $uclid5_invcnt))"

#Count #ln
echo "Boogie #ln: $(cat $b | wc -l)"
echo "UCLID5 #ln: $(cat $u | wc -l)"

