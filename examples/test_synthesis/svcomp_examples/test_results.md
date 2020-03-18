CVC4 version 1.8 pre-release [git HEAD 9a871003]

##  successful tests:
cegis_danger_benchmark_svcomp_multivar_true-unreach-call1.ucl.output: 
`(y == x)`
cegis_danger_benchmark_svcomp_underapprox_true-unreach-call1.ucl.output: 
`(((0bv32 == x) && (1bv32 == y)) || ((1bv32 == x) && (2bv32 == y)) || ((6bv32 == x) && (64bv32 == y)) || ((2bv32 == x) && (4bv32 == y)) || ((3bv32 == x) && (8bv32 == y)) || ((4bv32 == x) && (16bv32 == y)) || ((5bv32 == x) && (32bv32 == y)))`
cegis_danger_benchmark_svcomp_underapprox_true-unreach-call2.ucl.output: 
`(((0bv32 == x) && (1bv32 == y)) || ((1bv32 == x) && (2bv32 == y)) || ((6bv32 == x) && (64bv32 == y)) || ((2bv32 == x) && (4bv32 == y)) || ((4bv32 == x) && (16bv32 == y)) || ((3bv32 == x) && (8bv32 == y)) || ((5bv32 == x) && (32bv32 == y)))`

## Errors 
cegis_danger_benchmark_svcomp_phases_true-unreach-call2.ucl - division not supported
cegis_danger_benchmark_svcomp_simple_true-unreach-call3.ucl - division not supported 
cegis_danger_benchmark_svcomp_simple_true-unreach-call2.ucl.output - parser does not parse the result “true”
cegis_danger_benchmark_svcomp_const_true-unreach-call1.ucl.output - parser error: bvslt not supported
cegis_danger_benchmark_svcomp_simple_true-unreach-call1.ucl.output - parser error: let not supported
cegis_danger_benchmark_svcomp_simple_true-unreach-call4.ucl.output - parser error: let not supported

## Timed out (6 mins):
remainder
