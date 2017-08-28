from Arch.objects import *
from Arch.translator import translate


from PathExploring import * 
from ModelingFramework import Encoder
from z3 import *

if __name__ == '__main__':
	P1 = '''
	mov r1, #1
	str r1, [x]
	str r1, [y]
	'''
	P2 = '''
	L:
	ldr r1, [y]
	cmp r1, #1
	bne L
	ldr r1, [x]
	assert(r1 = #1)
	'''
	[P1, P2] = translate([P1, P2])
	# for e in P2:
	# 	print e
	
	P1 = GraphPreparation(P1)
	P2 = GraphPreparation(P2)
	X = pathExploring([P1,P2], 1)
	for p in X:
		# encode 
		e = Encoder.encode(p, 'gharachorloo', 'SC')
		# SMT solver
		s = Solver()
		s.add(e)
		result = s.check()
		print result