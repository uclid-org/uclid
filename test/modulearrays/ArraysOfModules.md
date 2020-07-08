# Overview
We will support array declarations like
```
instances ms : [integer]M(a : (x));
```
where `M` is a module, `M` has a boolean `input` named `a` and an integer `var` named `b`, and `x` is an array of booleans indexed by integers (`[integer]boolean`). Note the slightly subtle use of `x`.

The array `ms` will be rewritten to
```
var ms_a : [integer]boolean;
var ms_b : [integer]integer;
```
and `ms_a` will be associated with `x` (e.g. `ms_a = x` will occur in the `init` block).

Uses of `ms`, like
```
assume(ms[0].a == true);
```
will be rewritten to uses of the new array variable
```
assume(ms_a[0] == true);
```

# Details/Notes
- We create an array for everything the `ModuleFlattener` flattens.
- Need to take special care with "instance procedure map"

# TODO
- multiple calls to next with different arguments?