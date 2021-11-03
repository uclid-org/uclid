
This is an example of control synthesis using an oracle. The file specifies that a floating point controller for a DC motor must be stable, and that the state values must fall inside a safety specification
up to a certain unrolling limit. 

UCLID generates files for a SyMO[1] solver. To generate the file, run:

```
uclid test-control.ucl -y "delphi" -g "delphi_file"
```

To run Delphi on the resulting file, run:

```
delphi delphi_file.sl
```

Note that to run these files you must have following the installation instructions in the artifact readme. 