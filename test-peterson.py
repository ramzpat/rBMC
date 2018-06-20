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
	'''
	return translate([P1,P2])

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
			
			InstrOps(
				# cnt += 1
				TempReg('val') << AuxVar('cnt'),
				TempReg('val') << TempReg('val') + 1,
				AuxVar('cnt') << TempReg('val'),
				# Assert(cnt = 1)
				TempReg('val') << AuxVar('cnt'),
				Assertion(TempReg('val') == 1),
				# cnt -= 1
				TempReg('val') << AuxVar('cnt'),
				TempReg('val') << TempReg('val') - 1,
				AuxVar('cnt') << TempReg('val'),
			),

			# mpcore_data_memory_barrier();
			# *p_lock = 0;
			# mpcore_data_sync_barrier();
			InstrOps(
				hFW.DMB()
				),
			InstrOps(	# str r2, [lock]
				Location('lock') << 1,
				),
			InstrOps(
				hFW.DSB()
				),
			)

	
	return [P1, P1]


def toppers2():
	P1 ='''
	moveq r2, #1
	'''
	return translate([P1])
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
			# Assertion(False)
			)
	return [P1, P1]

def dekker():
	P1 = '''
		mov r1, #1 		; true
		mov r2, #0		; false
		mov r5, #1		; j
		str r1, [xi]	; [xi] := true
		do{
			ldr r3, [xj]
			cmp r3, #1
			; while(x[j] = true)
			if (z = #1){
				ldr r4, [k]
				cmp r4, r5
				; if turn == j:
				if (z = #1) {
					str r2, [xi]	; [xi] := false
					do{
						ldr r4, [k]
						cmp r4, r5
						assume(z = #0)	; should not stuck here.... for entering the CS
						{ ((z = #1) or (z = #0)) }
					}while(z = #1) 	; while(turn == j);
					str r1, [xi]	; [xi] := true
				}
				ldr r3, [xj]
				cmp r3, #1
			}
			assume(z = #0)
			{ ((z = #1) or (z = #0)) }
		}while(z = #1)
	'''

	P2 = '''
		mov r1, #1 		; true
		mov r2, #0		; false
		mov r5, #0		; i
		str r1, [xj]	; [xj] := true
		do{
			ldr r3, [xi]
			cmp r3, #1
			; while(x[i] = true)
			if (z = #1){
				ldr r4, [k]
				cmp r4, r5
				; if turn == i:
				if (z = #1) {
					str r2, [xj]	; [xj] := false
					do{
						ldr r4, [k]
						cmp r4, r5
						assert(z = #1) 	; should stuck here 
						{ ((z = #1) or (z = #0)) }
					}while(z = #1) 	; while(turn == i);
					str r1, [xj]	; [xj] := true
				}
				ldr r3, [xi]
				cmp r3, #1
			}
			assert(z = #1)	; should stuck here 
			{ ((z = #1) or (z = #0)) }
		}while(z = #1)

		;assert(false)
	'''


	return translate([P1, P2])

def perterson():
	P1 = '''
	mov r6, #0 
	mov r1, #1
	str r1, [f0]
	str r1, [turn]	; turn := 1

	do{
		ldr r2, [f1]
		cmp r2, #1
		;while flag[1] = true & turn = 1
		if ( z = #1 ) {
			ldr r3, [turn]
			cmp r3, #1
		}
	{ (z = #1) or (z = #0)} 
	}while( z = #1 )
	assert(false)
	'''

	P2 = ''' 
	mov r6, #0
	mov r1, #1
	str r1, [f1]
	str r6, [turn]	; turn := 0

	do{
		ldr r2, [f0]
		cmp r2, #1
		;while flag[1] = true & turn = 0
		if(z = #1){
			ldr r3, [turn]
			cmp r3, #0
		}
	{ (z = #1) or (z = #0)} 
	}while( z = #1 )
	assert(false)	'''
	return [P1, P2]

def aux_test():
	P1 = seqOpsNode(
		InstrOps(
			# cnt += 1
			TempReg('val') << AuxVar('cnt'),
			TempReg('val') << TempReg('val') + 1,
			AuxVar('cnt') << TempReg('val'),
			# Assert(cnt = 1)
			TempReg('val') << AuxVar('cnt'),
			Assertion(TempReg('val') == 1),
			# cnt -= 1
			TempReg('val') << AuxVar('cnt'),
			TempReg('val') << TempReg('val') - 1,
			AuxVar('cnt') << TempReg('val'),
		),
		)
	# print AuxVar('cnt') << 1

	return [P1,P1]

def aux_test_arm():
	P1 = '''
	mov r6, #0 
	mov r1, #1
	str r1, [f0]
	str r1, [turn]	; turn := 1

	do{
		ldr r2, [f1]
		cmp r2, #1
		;while flag[1] = true & turn = 1
		if ( z = #1 ) {
			ldr r3, [turn]
			cmp r3, #1
		}
	{ (z = #1) or (z = #0)} 
	}while( z = #1 )
	'''

	P2 = ''' 
	mov r6, #0
	mov r1, #1
	str r1, [f1]
	str r6, [turn]	; turn := 0

	do{
		ldr r2, [f0]
		cmp r2, #1
		;while flag[0] = true & turn = 0
		if(z = #1){
			ldr r3, [turn]
			cmp r3, #0
		}
	{ (z = #1) or (z = #0)} 
	}while( z = #1 )
	'''
	p = translate([P1,P2])
	p[0] << seqOpsNode(
		InstrOps(
			# cnt += 1
			TempReg('val') << AuxVar('cnt'),
			TempReg('val') << TempReg('val') + 1,
			AuxVar('cnt') << TempReg('val'),
			# Assert(cnt = 1)
			TempReg('val') << AuxVar('cnt'),
			Assertion(TempReg('val') == 1),
			# cnt -= 1
			TempReg('val') << AuxVar('cnt'),
			TempReg('val') << TempReg('val') - 1,
			AuxVar('cnt') << TempReg('val'),
		),
		InstrOps(
			# flag[0] = false
			Location('f0') << 0
		)
		)
	p[1] << seqOpsNode(
		InstrOps(
			# cnt += 1
			TempReg('val') << AuxVar('cnt'),
			TempReg('val') << TempReg('val') + 1,
			AuxVar('cnt') << TempReg('val'),
			# Assert(cnt = 1)
			TempReg('val') << AuxVar('cnt'),
			Assertion(TempReg('val') == 1),
			# cnt -= 1
			TempReg('val') << AuxVar('cnt'),
			TempReg('val') << TempReg('val') - 1,
			AuxVar('cnt') << TempReg('val'),
		),
		InstrOps(
			# flag[1] = false
			Location('f1') << 0
		)
		)




		# print AuxVar('cnt') << 1

	return p

if __name__ == '__main__':
	# P = aux_test()
	P = aux_test_arm()
	# P = mp()
	# P = mp_fence()
	# P = toppers()
	# P = toppers2()
	# P = sparc()
	# P = dekker()

	
	# print 'program to be checked'
	# for p in P:
	# 	for i in p:
	# 		print i
	# 	print '----------'


	for i in range(0, len(P)):
		print 'preparing program ', str(i+1)
		P[i] = invExtractor(P[i])
		P[i] = GraphPreparation(P[i])


	print 'finish preparing'
	X = pathExploring(P)
	print 'finish exploring'

	for model in ['TSO', 'SC', 'ARM']:
	# for model in ['SC']:
		print 'experiment with model ', model
		k = 0
		for p in pathExploring(P):
			k = k + 1

			# encode 
			# print '---- checking the follwing programs'
			# for e in p:
			# 	print e
			# print '------'

			start = time.clock()
			# e = Encoder.encode(p, 'gharachorloo', model)
			# # e = Encoder.encode(p, 'gharachorloo', 'TSO')
			# # e = Encoder.encode(p, 'gharachorloo', 'PSO')
			# e = Encoder.encode(p, 'herding_cats', 'SC')

			# # e = Encoder.encode(p, 'herding_cats', 'TSO')
			e = Encoder.encode(p, 'herding_cats', model)
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
			if result == sat:
				# print result
				# for e in P:
				# 	for i in e:
				# 		print i
					# print '------'
				break
	