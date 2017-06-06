# rBMC - relaxed Bounded Model Checking
rBMC is an experimental tool for verifying a list of assembly programs under a relaxed memory model. The tool adopts a bounded model checking approach [2] to deal with the loop occuring in assembly source code.

# Supported Memory Models
This work adopts a framework provided by Characholoo [1]. The current support memory models are:
- SC
- TSO+
- PSO+

# Usage
``
python rbmc.py \<bound_k\> \<memory_model\> \<syntax\> \{ \<input_file\> \}+
``
## Example
```
python rbmc.py 1 PSO+ arm examples/ARM/mp*
```
or
```
python rbmc.py 1 PSO+ arm examples/ARM/mp1 examples/ARM/mp2 
```
It results 
```
Invalid under PSO+
================= Nomalize Programs ======================
====== Thread #0
if(True)['r1_0 := 1; ']
if(True)['store(r1_0,X); ']
if(True)['store(r1_0,Y); ']
====== Thread #1
if(True)['r2_0 := load(Y); ']
if(True)['r3_0 := load(X); ']
if(True)['assume((r2_0 == 1)); ']
if(True)['assert((r3_0 == 1)); ']
================= Memory operations ======================
==== Memory operations on Proc P0
> Reads:
> Writes:
  "write_0"      represents      "store(r1_0,X)"
  "write_1"      represents      "store(r1_0,Y)"
==== Memory operations on Proc P1
> Reads:
  " read_0"      represents      "r2_0 := load(Y)"
  " read_1"      represents      "r3_0 := load(X)"
> Writes:
================= Trace ======================
==== Trace on processor P0
[subOpr(write(write_1), P0), subOpr(write(write_0), P0)]
==== Trace on processor P1
[subOpr(write(write_1), P1), subOpr(read(read_0), P1), subOpr(read(read_1), P1), subOpr(write(write_0), P1)]
```


## Experiment
\<to-do\>


# References 
[1] K. Gharachorloo, “Memory Consistency Models for Shared-Memory Multiprocessors.” Stanford University, 1995.\n
[2] A. Armando, J. Mantovani, and L. Platania, “Bounded Model Checking of Software Using SMT Solvers Instead of SAT Solvers,” Springer Berlin Heidelberg, 2006, pp. 146–162.
