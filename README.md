# rBMC - relaxed Bounded Model Checking
rBMC is an experimental tool for verifying a list of assembly programs under a relaxed memory model. The tool adopts a bounded model checking approach [2] to deal with the loop occuring in assembly source code.

# Supported Memory Models
This work adopts a framework provided by Characholoo [1]. The current support memory models are:
- SC
- TSO+
- PSO+

# Usage
``
python rbmc.py <bound_k> <memory_model> <syntax> { <input_file> }+
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
<table>
  <tr>
    <td> </td>
    <td colspan="3">Run time</td>
    <td colspan="3">Finding bug</td>
  </tr>
  <tr>
    <td> Algoithm (bound) </td>
    <td>SC</td>
    <td>TSO</td>
    <td>PSO</td>
    <td>SC</td>
    <td>TSO</td>
    <td>PSO</td>
  </tr>
  <tr>
    <td> Message passing (1)</td>
    <td> 0.192 </td>
    <td> 0.313 </td>
    <td> 0.580 </td>
    <td> n </td>
    <td> n </td>
    <td> y </td>
  </tr>
  <tr>
    <td> SPARC Spinlock (1)</td>
    <td> 6.565  </td>
    <td> 7.415  </td>
    <td> 7.436 </td>
    <td> n </td>
    <td> n </td>
    <td> n </td>
  </tr>
  <tr>
    <td> Dekker (1)</td>
    <td> 2.379 </td>
    <td> 2.763 </td>
    <td> 2.796 </td>
    <td> n </td>
    <td> y </td>
    <td> y </td>
  </tr>
  <tr>
    <td> Peterson (1)</td>
    <td> 2.791 </td>
    <td> 72.466 </td>
    <td> 92.666 </td>
    <td> n </td>
    <td> y </td>
    <td> y </td>
  </tr>
  <tr>
    <td> Known PSO bug (0)</td>
    <td> 3.326  </td>
    <td> 39.320  </td>
    <td> 1538.227 </td>
    <td> n </td>
    <td> n </td>
    <td> y </td>
  </tr>
</table>




# References 
[1] K. Gharachorloo, “Memory Consistency Models for Shared-Memory Multiprocessors.” Stanford University, 1995.\n
[2] A. Armando, J. Mantovani, and L. Platania, “Bounded Model Checking of Software Using SMT Solvers Instead of SAT Solvers,” Springer Berlin Heidelberg, 2006, pp. 146–162.
