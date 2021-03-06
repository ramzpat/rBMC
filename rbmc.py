# RBMC
import sys 
# reading input files
# usage: python rbmc.py <k> <memory model> {<input file>}+
bound_k = 0
memory_model = 'sc'
input_files = []
syntax = 'arm'

if len(sys.argv) < 4:   
	print 'error'
	sys.exit()

bound_k = int(sys.argv[1])
memory_model = sys.argv[2]
syntax = sys.argv[3]
input_files = sys.argv[4:]
nProc = len(input_files)


__modelList = ['SC','TSO+','PSO+']
__systaxList = ['arm', 'sparc']


if not( memory_model in __modelList ):
	raise Exception('This tool currently supports only SC, TSO+, and PSO+ memory models')

if not( syntax in __systaxList ):
	raise Exception('This tool currently supports only arm and sparc syntax (not complete yet)')


prog = []
for file in input_files:
	with open(file, 'r') as myfile:
	    prog += [myfile.read()]


import verifier
import z3
(result, info, programs, model) = verifier.verify(prog, syntax, memory_model, bound_k)
print "%s under %s"%("Valid" if (result != z3.sat) else "Invalid",memory_model)
if result == z3.sat:
	verifier.counter_example(programs, info, model)
