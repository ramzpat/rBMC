
from HWModel.OperatorSem import *
from Arch.arch_object import *

def invExtractor(P):
	# build Code Structure

	# 1 - extract Operations as linear ? except parallel ?
	# assert(not isinstance(P, ParallelSem))
	ret = CodeStructure(SeqSem(), [])
	for p in P.list():
		if isinstance(p, SeqSem):
			# i = invExtractor(p)
			ret += p
		if isinstance(p, DoWhile):
			# 'do-while'
			# ret += CodeStructure(p)
			loopBody = invExtractor(p.body)
			loopBody2 = loopBody + SeqSem(
				Assertion(p.inv),
				havoc(0),
				Assume(p.inv)
				)
			loopBody2 += loopBody
			loopBody2 = loopBody2 + CodeStructure(SeqSem(), [
					CodeStructure( SeqSem(Assume(False), Assertion('p.Q')) ),
					CodeStructure( SeqSem(Assertion('p.inv')) )
				])
			ret += loopBody2
		elif isinstance(p,Operation):
			ret += p
		elif isinstance(p,AnnotatedStatement):
			ret += p
	# for p in ret.body:
	# 	print p

	return ret

def mp():
	P1 = SeqSem(
		InstrSem(	# mov r1, #1
			TempReg('val') << 1, 
			Register('r1') << TempReg('val')
			),
		InstrSem(	# str r1, [x]
			TempReg('val') << Register('r1'),
			ParallelSem(TempReg('val1') << Register('r2'), TempReg('val2') << Register('r2')),
			Location('x') << TempReg('val')
			),
		InstrSem(	# str r1, [y]
			TempReg('val') << Register('r1'),
			Location('y') << TempReg('val')
			)
		)

	P2 = SeqSem(
		DoWhile(		# L:
			SeqSem(
			DoWhile(		# L:
				InstrSem(	# ldr r2, [y]
					TempReg('xal') << Location('y'),
					Register('X2') << TempReg('val')
					),

				(Register('n') == 0),						# { inv }
				Register('n') == 0,			# bne L
				Register('n') == 1			# { Q }
			), 
			InstrSem(	# cmp r2, #1
				ParallelSem(
					TempReg('rd') << 1,
					TempReg('rt') << Register('r2')
				),
				ParallelSem(
					Register('z') << i_if_exp(TempReg('rd') == TempReg('rt'), 1, 0),
					Register('n') << i_if_exp(TempReg('rd') == TempReg('rt'), 0, 1),
				)
			)),
			(Register('z') == 0),						# { inv }
			Register('z') == 0,			# bne L
			Register('z') == 1			# { Q }
		), 
		InstrSem(	# ldr r3, [x]
			TempReg('val') << Location('x'),
			Register('r3') << TempReg('val')
			),
		Assertion(Register('r3') == 1)
		)
	# print P2
	print '+++++++'
	ret = invExtractor(P2)
	for p in ret:
		print p
		print '----'
	pass 

if __name__ == '__main__':
	mp()
	pass 