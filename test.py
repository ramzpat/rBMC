from Arch.objects import *
from Arch.translator import translate


from PathExploring import * 
from ModelingFramework import Encoder
from z3 import *

import time

if __name__ == '__main__':
	P1 = '''
	mov r1, #1
	str r1, [x]
	str r1, [y]
	'''
	P2 = '''
	L:
	;do{
		ldr r1, [y]
	;{ (r1 = #0 or r1 = #1) }
	;}while( r1 = #0 )
	;assume( r1 = #1)
	cmp r1, #1
	bne L
	; ldr r1, [x]
	assert([x] = #1)
	'''
	[P1, P2] = translate([P1, P2])
	# P2 << OpsNode(Assertion(Location('x') == 1))
	# for e in P2.exploreNodes():
	# 	print '=',e.ops

	# exit()
	# for o in P2:
	# 	print o
	P2 = invExtractor(P2)
	# for o in P2:
	# 	print o
	# exit()

	P1 = GraphPreparation(P1)
	P2 = GraphPreparation(P2)


	X = pathExploring([P1,P2], 20)
	for p in X:

		# print p[0],p[1]
		# encode 
		# e = Encoder.encode(p, 'gharachorloo', 'SC')
		e = Encoder.encode(p, 'gharachorloo', 'TSO')
		# e = Encoder.encode(p, 'gharachorloo', 'PSO')
		# e = Encoder.encode(p, 'herding_cats', 'SC')
		# e = Encoder.encode(p, 'herding_cats', 'ARM')
		# # SMT solver

		s = Solver()
		s.add(e)

		start = time.clock()
		result = s.check()
		elapsed = (time.clock() - start)
		print ',solving time, ', elapsed, ',s.'
		# print result
		if result == sat:
			# print p[1]
			break
