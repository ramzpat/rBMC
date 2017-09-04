# RBMC
import sys 
# reading input files
# usage: python rbmc.py <k> <fw> <memory model> {<input file>}+
bound_k = 0
memory_model = 'sc'
input_files = []
syntax = 'arm'

if len(sys.argv) < 5:   
	print 'error'
	sys.exit()

bound_k = int(sys.argv[1])
fw = sys.argv[2]
memory_model = sys.argv[3]
syntax = sys.argv[4]
input_files = sys.argv[5:]
nProc = len(input_files)


__modelList = ['SC','TSO+','PSO+']
__systaxList = ['arm', 'sparc']


# if not( memory_model in __modelList ):
	# raise Exception('This tool currently supports only SC, TSO+, and PSO+ memory models')

if not( syntax in __systaxList ):
	raise Exception('This tool currently supports only arm and sparc syntax (not complete yet)')


prog = []
for file in input_files:
	with open(file, 'r') as myfile:
	    prog += [myfile.read()]


from Arch.objects import *
from Arch.translator import translate


from PathExploring import * 
from ModelingFramework import Encoder
from z3 import *

# intermediate representation (operation structure)
prog = translate(prog, syntax)

for i in range(0, len(prog)):
	prog[i] = GraphPreparation(prog[i])
X = pathExploring(prog, bound_k)

for p in X:
	# encode 
	e = Encoder.encode(p, fw, memory_model)
	# SMT solver
	s = Solver()
	s.add(e)
	result = s.check()
	if result == z3.sat:
		print 'Invalid'
		print '========= Execution Path ========='
		for t in p:
			print t
if result == z3.unsat:
	print 'Valid under bound', bound_k



# import verifier
# import z3
# (result, info, programs, model) = verifier.verify(prog, syntax, memory_model, bound_k)
# print "%s under %s"%("Valid" if (result != z3.sat) else "Invalid",memory_model)
# if result == z3.sat:
# 	verifier.counter_example(programs, info, model)
