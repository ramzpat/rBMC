from Arch.objects import *
from Arch.translator import translate


from PathExploring import * 
from ModelingFramework import Encoder
from z3 import *


import ModelingFramework.Frameworks.gharachorloo  as gFW
import ModelingFramework.Frameworks.herdingCats as hFW 

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
	assert(r1 = #2)
	'''
	return translate([P2])

def mp_fence():
	P1 = seqOpsNode(
			InstrOps(	# mov r1, #1
				TempReg('val') << 1, 
				Register('r1') << TempReg('val')
				),
			InstrOps(	# str r1, [x]
				TempReg('val') << Register('r1'),
				Location('x') << TempReg('val')
				),
			# fence ?
			InstrOps(	# STBar 
				hFW.MFence(),
				gFW.STBarFence(),
				hFW.DMB()
				),
			InstrOps(	# str r1, [y]
				TempReg('val') << Register('r1'),
				Location('y') << TempReg('val')
			))

	P2 = seqOpsNode(
			DoWhile(
				SeqOps(
					InstrOps(	# ldr r2, [y]
						TempReg('val') << Location('y'),
						Register('r2') << TempReg('val')
						),
					InstrOps(	# cmp r2, #1
						ParOps(
							TempReg('rd') << 1,
							TempReg('rt') << Register('r2')
						),
						ParOps(
							SeqOps(
								TempReg('val_z') << ifExp(TempReg('rd') == TempReg('rt'), 1, 0),
								Register('z') << TempReg('val_z')
							),
							SeqOps(
								TempReg('val_n') << ifExp(TempReg('rd') == TempReg('rt'), 0, 1),
								Register('n') << TempReg('val_n')
							)
						)
					),
				),
				((Register('n') == 1) | (Register('n') == 0)),
				Register('n') == 1
			),
			InstrOps(	# STBar 
				hFW.STBarFence(),
				gFW.STBarFence(),
				hFW.DMB()
				),
			InstrOps(	# ldr r1, [x]
				TempReg('val') << Location('x'),
				Register('r1') << TempReg('val')
			),
			Assertion(Register('r1') == 1)
		)
	return [P1, P2]
def toppers():
	P1 = seqOpsNode(
			# LabelStm('While'),
			DoWhile(
				SeqOps(
					InstrOps(	# mov r2, #1
						TempReg('val') << 1, 
						Register('r2') << TempReg('val'),
						),
					InstrOps(	# ldrex r1, [lock]
						OprLoadLink(TempReg('val'), Location('lock')),
						Register('r1') << TempReg('val'),
						),
					InstrOps(	# cmp r1, #0
						TempReg('rd') << Register('r1'),
						TempReg('rt') << 0,
						TempReg('val_z') << ifExp(TempReg('rd') == TempReg('rt'), 1, 0),
						TempReg('val_n') << ifExp(TempReg('rd') == TempReg('rt'), 0, 1),
						Register('z') << TempReg('val_z'),
						Register('n') << TempReg('val_n')
						),
					InstrOps(	# strexeq r1, r2, [lock]
							CondOps( Register('z') == 1,
								SeqOps(
									TempReg('val') << Register('r2'),
									OprStoreCond(TempReg('res'), Location('lock'), TempReg('val')),
									Register('r1') << TempReg('res')
									))
						),
					InstrOps(	# mov r'output',r1
						TempReg('val') << Register('r1'),
						Register('output') << TempReg('val')
						)
				),
				(Register('output') == 1) | (Register('output') == 0),
				(Register('output') == 1)
			),
			InstrOps(
				hFW.DMB()
				),
			# can lock 
			Assertion(False)
			# Assertion(Register('output') == 1)
			)

	
	return [P1, P1]

def sparc():
	P1 = seqOpsNode(
			InstrOps(	# ldstub [lock], r5
				Atomic(TempReg('val') << Location('lock')), 
				Register('r5') << TempReg('val'),
				Atomic(Location('lock') << 1),
			),
			IfBr( ~ (Register('r5') == 0), 
				SeqOps(
					DoWhile(
						SeqOps(
							
							IfBr( ~ (Register('r5') == 0), 
									SeqOps(
										DoWhile(
											SeqOps(
												InstrOps(	# ldub [lock], r5
														TempReg('val') << Location('lock'),
														Register('r5') << TempReg('val')
													),
											),
											(Register('r5') == 0) | (Register('r5') == 1), 
											~ (Register('r5') == 0)
										)
									),
								),

							InstrOps(	# ldstub [lock], r5
								Atomic(TempReg('val') << Location('lock')), 
								Register('r5') << TempReg('val'),
								Atomic(Location('lock') << 1),
								),

							
						),
						(Register('r5') == 0) | (Register('r5') == 1),
						~ (Register('r5') == 0)
					)
				)
			),
			# LabelStm('CS'),
			Assertion(False)
			)
	return [P1, P1]

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
	# P = mp()
	# P = mp_fence()
	# P = toppers()
	P = sparc()
	
	# P2 << OpsNode(Assertion(Location('x') == 1))
	# for e in P2.exploreNodes():
	# 	print '=',e.ops

	# exit()
	# for o in P3:
	# 	print o
	for i in range(0, len(P)):
		print 'preparing program ', str(i+1)
		P[i] = invExtractor(P[i])
		P[i] = GraphPreparation(P[i])
	# P2 = invExtractor(P3)

	# for o in P2:
	# 	print o
	# exit()

	# P1 = GraphPreparation(P1)
	# P2 = GraphPreparation(P2)

	print 'finish preparing'
	X = pathExploring(P)
	print 'finish exploring'
	k = 0
	for p in X:
		k = k + 1

		# encode 
		# for e in p:
		# 	print e
		# print '------'

		start = time.clock()
		e = Encoder.encode(p, 'gharachorloo', 'SC')
		# e = Encoder.encode(p, 'gharachorloo', 'TSO')
		# e = Encoder.encode(p, 'gharachorloo', 'PSO')
		# e = Encoder.encode(p, 'herding_cats', 'SC')
		# e = Encoder.encode(p, 'herding_cats', 'TSO')
		# e = Encoder.encode(p, 'herding_cats', 'ARM')
		elapsed = (time.clock() - start)
		print k,',encoding time, ', elapsed, ',s.',


		# # SMT solver
		s = Solver()
		s.add(e)

		start = time.clock()
		result = s.check()
		elapsed = (time.clock() - start)
		print ',solving time, ', elapsed, ',s.', 
		print result
		# if result == sat:
		# 	# print result
		# 	for e in P:
		# 		for i in e:
		# 			print i
		# 		print '------'
		# 	break
	print k
