
from HWModel.OperatorSem import *
from Arch.arch_object import *


def invExtractor(P, vars = [], clss = SeqSem):
	# build Code Structure

	# 1 - extract Operations as linear ? except parallel ?
	# assert(not isinstance(P, ParallelSem))
	ret = CodeStructure(clss(), [])
	# ret = emptyCS()
	# print P
	for p in P.list():
		# if-Extractor
		if isinstance(p, IfStm):
			cond = p.cond 
			# sem = p.sem
			sem = invExtractor(SeqSem(*p.sem), vars, SeqSem)
			
			mergePoint = CodeStructure(SeqSem())

			# print 'mPoint'
			# print mergePoint
			fCS = CodeStructure(SeqSem( Assume(~ cond)), [mergePoint])
			tCS = CodeStructure(SeqSem( Assume(cond),*(sem)), [mergePoint])
			separatePoint = CodeStructure(SeqSem(), [tCS, fCS])			

			ret << separatePoint
		elif isinstance(p, SeqSem):
			i = p
			i = invExtractor(p, vars, p.__class__)
			# if ret.__class__ == emptyCS:
			# 	ret = i
			# else:
			# 	ret << i
			ret << i
		elif isinstance(p, DoWhile):
			# 'do-while'
			# ret += CodeStructure(p)
			loopBody = invExtractor(p.body, vars, p.body.__class__)
			loopBody2 = loopBody + SeqSem(
				Assertion(p.inv),
				havoc(*vars),
				Assume(p.inv),
				Assume(p.bInstr)
				)
			loopBody2 += loopBody
			loopBody2 += CodeStructure(SeqSem(), [
					CodeStructure( SeqSem(Assume(~(p.bInstr)), Assertion(p.Q)) ),
					CodeStructure( SeqSem(Assertion(p.inv)) )
				])
			ret << loopBody2
		elif isinstance(p,Operation):
			# ret += p
			
			# if ret.__class__ == emptyCS:
			# 	ret = p
			# else:
			ret << p

		elif isinstance(p,AnnotatedStatement):
			ret << p
	# for p in ret.body:
	# 	print p

	return ret


def mp():
	P1 = SeqSem(
		InstrSem(	# mov r1, #1
			TempReg('val') << 1, 
			Register('r1') << TempReg('val')
			),
		IfStm( TempReg('val') == 1,
		InstrSem(	# str r1, [x]
			TempReg('val') << Register('r1'),
			ParallelSem(TempReg('val1') << Register('r2'), TempReg('val2') << Register('r2')),
			Location('x') << TempReg('val')
			)),
		InstrSem(	# str r1, [y]
			TempReg('val') << Register('r1'),
			Location('y') << TempReg('val')
			)
		)

	P2 = SeqSem(
		DoWhile(		# L:
			SeqSem(
				DoWhile(
					InstrSem(	# ldr r2, [y]
						TempReg('xal') << Location('y'),
						Register('X2') << TempReg('val')
						),
						(Register('z') == 0),						# { inv }
					Register('z') == 0,			# bne L
					Register('z') == 1			# { Q }
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

	print '+++++++'
	ret = invExtractor(P1, [Register('x')])
	for p in ret:
		print p
		print '----'
	pass 

if __name__ == '__main__':
	mp()
	pass 