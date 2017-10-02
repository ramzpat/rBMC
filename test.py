from Arch.objects import *
from Arch.translator import translate


from PathExploring import * 
from ModelingFramework import Encoder
from z3 import *

import time

def mp():
	P1 = '''
	mov r1, #1
	str r1, [x]
	str r1, [y]
	'''

	P2 = '''
	do {
		ldr r1, [y]
		cmp r1, #1
	{ (n = #0 or n = #1) }
	} while ( n = #1 ) 
	ldr r1, [x]
	assert(r1 = #1)
	'''
	return translate([P1, P2])

def mp_fence():
	P1 = '''
	mov r1, #1
	str r1, [x]
	str r1, [y]
	'''

	P2 = '''
	do {
		ldr r1, [y]
		cmp r1, #1
	{ (n = #0 or n = #1) }
	} while ( n = #1 ) 
	ldr r1, [x]
	assert(r1 = #1)
	'''
	return [P1, P2]
def toppers():
	P1 = '''
	mov r1, #1
	str r1, [x]
	str r1, [y]
	'''

	P2 = '''
	do {
		ldr r1, [y]
		cmp r1, #1
	{ (n = #0 or n = #1) }
	} while ( n = #1 ) 
	ldr r1, [x]
	assert(r1 = #1)
	'''
	return [P1, P2]

def sparc():
	P1 = '''
	mov r1, #1
	str r1, [x]
	str r1, [y]
	'''

	P2 = '''
	do {
		ldr r1, [y]
		cmp r1, #1
	{ (n = #0 or n = #1) }
	} while ( n = #1 ) 
	ldr r1, [x]
	assert(r1 = #1)
	'''
	return [P1, P2]

def dekker():
	P1 = '''
	mov r1, #1
	str r1, [x]
	str r1, [y]
	'''

	P2 = '''
	do {
		ldr r1, [y]
		cmp r1, #1
	{ (n = #0 or n = #1) }
	} while ( n = #1 ) 
	ldr r1, [x]
	assert(r1 = #1)
	'''
	return [P1, P2]

def perterson():
	P1 = '''
	mov r1, #1
	str r1, [x]
	str r1, [y]
	'''

	P2 = '''
	do {
		ldr r1, [y]
		cmp r1, #1
	{ (n = #0 or n = #1) }
	} while ( n = #1 ) 
	ldr r1, [x]
	assert(r1 = #1)
	'''
	return [P1, P2]

if __name__ == '__main__':
	P = mp()
	
	# P2 << OpsNode(Assertion(Location('x') == 1))
	# for e in P2.exploreNodes():
	# 	print '=',e.ops

	# exit()
	# for o in P3:
	# 	print o
	for i in range(0, len(P)):
		P[i] = invExtractor(P[i])
		P[i] = GraphPreparation(P[i])
	# P2 = invExtractor(P3)

	# for o in P2:
	# 	print o
	# exit()

	# P1 = GraphPreparation(P1)
	# P2 = GraphPreparation(P2)


	X = pathExploring(P)
	for p in X:

		# encode 
		start = time.clock()
		# e = Encoder.encode(p, 'gharachorloo', 'SC')
		# e = Encoder.encode(p, 'gharachorloo', 'TSO')
		# e = Encoder.encode(p, 'gharachorloo', 'PSO')
		e = Encoder.encode(p, 'herding_cats', 'SC')
		# e = Encoder.encode(p, 'herding_cats', 'TSO')
		# e = Encoder.encode(p, 'herding_cats', 'ARM')
		elapsed = (time.clock() - start)
		print ',encoding time, ', elapsed, ',s.'


		# # SMT solver
		s = Solver()
		s.add(e)

		start = time.clock()
		result = s.check()
		elapsed = (time.clock() - start)
		print ',solving time, ', elapsed, ',s.'
		print result
		if result == sat:
			# print result
			for e in P:
				for i in e:
					print i
				print '------'
			break
