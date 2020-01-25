CVC4 version 1.8 pre-release [git HEAD 9a871003]

##  successful tests:
test_basic.ucl.output: (i >= 0)
test_case.ucl.output: (i >= 0)
test_uninterpreted_func.ucl.output:(0 <= i)

## Errors 
test_axiom2.ucl.output: Axiom is not passed to CVC4, CVC4 says unknown:should be fixed
test_axioms.ucl.output: Axiom is not passed to CVC4, CVC4 says unknown: should be fixed
test_bitvector_sign.ucl.output: not sure why this doesn’t work
test_const.ucl.output: constant doesn’t get passed to the invariant function
test_infinite_arrays.ucl.output: CVC4 returns unknown, because the array is infinite

test_mixed_logic.ucl.output: unknown identifier bv_to_signed_int
test_mixed_logic2.ucl.output: unknown error bv_to_signed_int

## Timed out (6 mins):
test_arrays2.ucl
test_arrays3.ucl
test_arrays.ucl
test_exists.ucl
test_forall.ucl
test_infinite_arrays.ucl
test_multi_funcs.ucl
