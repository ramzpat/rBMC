
from HWModel.OperatorSem import *
from Arch.arch_object import *


def getAssnVars(p):
	if isinstance(p, Assertion):
		return []
	elif isinstance(p, Assume):
		return []
	elif isinstance(p, Assignment) and not(isinstance(p.var, TempReg)):
		return [p.var]
	elif isinstance(p, ParallelSem):
		newPar = []
		for i in p.list():
			newPar += getAssnVars(i)
		return newPar
	elif isinstance(p, IfStm):
		assnVars = []
		for i in p.list():
			assnVars += getAssnVars(i)
		# print SeqSem(*newSeq)
		return assnVars
	elif isinstance(p, SeqSem):
		newSeq = []
		for i in p.list():
			newSeq += getAssnVars(i)
		return newSeq
	elif isinstance(p, CodeStructure):
		v = []
		for i in p:
			v += getAssnVars(i)
		return v
	return []

def invExtractor(P, vars = [], clss = SeqSem):
	# build Code Structure

	# 1 - extract Operations as linear ? except parallel ?
	# assert(not isinstance(P, ParallelSem))
	clss = P.__class__
	if clss == IfStm:
		# ret = CodeStructure(IfStm(P.cond), [])
		cond = P.cond
		sem = invExtractor(SeqSem(*P.sem), vars, SeqSem)
		# mergePoint = CodeStructure(SeqSem())
		mergePoint = mergePointCS()
		fCS = CodeStructure(SeqSem( Assume(~ cond)), [mergePoint])
		tCS = (CodeStructure(SeqSem( Assume(cond))) + (sem))
		tCS.addMergePoint(mergePoint)
		separatePoint = CodeStructure(SeqSem(), [tCS, fCS])			

		ret = separatePoint
		return ret
	else:
		ret = CodeStructure(clss(), [])
	# ret = emptyCS()
	# print P
	for p in P.list():
		# if-Extractor
		if isinstance(p, IfStm):
			cond = p.cond 
			# sem = p.sem
			sem = invExtractor(SeqSem(*p.sem), vars, SeqSem)
			
			mergePoint = mergePointCS()
			# mergePoint = CodeStructure(SeqSem())

			# print 'mPoint'
			# print mergePoint
			fCS = CodeStructure(SeqSem( Assume(~ cond)), [mergePoint])
			tCS = (CodeStructure(SeqSem( Assume(cond))) + (sem))
			
			tCS.addMergePoint(mergePoint)

			# (CodeStructure(SeqSem( Assume(cond))) + (sem)) + mergePoint
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
			vars = getAssnVars(loopBody)
			vars = list(set(vars))
			# for v in vars:
			# 	print v

			loopBody2 = loopBody + SeqSem(
				Assertion(p.inv),
				havoc(*vars),
				Assume(p.inv),
				Assume(p.bInstr)
				)
			loopBody2 += loopBody

			# print '****************'
			# for i in loopBody2:
			# 	print i
			# # print loopBody2.next[0].next, loopBody2.next[1].next[0].next
			# print '****************'
			loopBody2 += CodeStructure(SeqSem(), [
					CodeStructure( SeqSem(Assume(~(p.bInstr)), Assertion(p.Q)) ),
					CodeStructure( SeqSem(Assertion(p.inv)), [terminateCS()] )
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