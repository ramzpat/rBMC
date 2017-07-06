
from HWModel.OperatorSem import *
from Arch.arch_object import *
from SMTEncoder import *

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
	# elif clss == RmwStm:
	# 	ret = CodeStructure(SeqSem(), [])
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


			# print mergePoint
			fCS = CodeStructure(SeqSem( Assume(~ cond), branchOp()), [mergePoint])
			tCS = CodeStructure(SeqSem( Assume(cond), branchOp())) 
			tCS << sem

			# print 'mPoint', ret.__class__
			# for u in tCS:
			# 	print u
			# print '------'
			tCS.addMergePoint(mergePoint)

			# (CodeStructure(SeqSem( Assume(cond))) + (sem)) + mergePoint
			separatePoint = CodeStructure(SeqSem(), [tCS, fCS])			
			
			
			ret << separatePoint
		elif isinstance(p, RmwStm):
			# print ret.body.__class__
			ret << CodeStructure(p)
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
				branchOp('T', 'T'),
				havoc(*vars),
				Assume(p.inv),
				Assume(p.bInstr),
				branchOp('T', 'T')
				)
			loopBody2 += loopBody

			# print '****************'
			# for i in loopBody2:
			# 	print i
			# # print loopBody2.next[0].next, loopBody2.next[1].next[0].next
			# print '****************'
			loopBody2 << CodeStructure(SeqSem(), [
					CodeStructure( SeqSem(Assume(~(p.bInstr)), branchOp('T', 'T'), Assertion(p.Q)) ),
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


def prepareDominators(p):
	nodes = set([i for i in p.exploreNodes()])
	rNodes = nodes - set([p])

	p.dominator = set([p])
	for n in rNodes:
		n.dominator = nodes
	isChange = True
	while isChange:
		isChange = False
		for n in rNodes:

			if len(n.pred) > 0:
				newN = set(nodes)
				for pr in n.pred:
					newN &= pr.dominator
			else:
				newN = set([])
			domN = set([n]).union( newN )

			if n.dominator - domN  != set([]):
				isChange = True 
			n.dominator = domN

	# for n in nodes:
	# 	print n.ops, n.dominator
	# print '------------'
	# for i in P:
		# print i.ops
		# i.ops = Ops()

def branchExtractor(P):
	assert(isinstance(P, OpsNode))

	# collect label
	def exploreLabel(p, ret = {}):
		assert(isinstance(p, OpsNode))
		# ret = {}
		if isinstance(p.ops, LabelStm):
			ret[str(p.ops)] = p
		for i in p.next:
			ret = exploreLabel(i, ret)
		return ret 
	labels = exploreLabel(P)


	def eliminateCond(p):
		assert(isinstance(p, Ops))
		for i in range(0, len(p.elements)):
			if isinstance(p.elements[i], CondOps):
				p.elements[i] = Ops()
			elif isinstance(p.elements[i], Ops):
				eliminateCond(p.elements[i])

	def realizeCond(p):
		assert(isinstance(p, Ops))
		for i in range(0, len(p.elements)):
			if isinstance(p.elements[i], CondOps):
				# print 'realize',p.elements[i].elements[0] 
				p.elements[i] = p.elements[i].elements[0]
			elif isinstance(p.elements[i], Ops):
				realizeCond(p.elements[i])


	# condition elimination 
	def editConditionNode(p):
		assert(isinstance(p, OpsNode))
		next = p.next 
		if isinstance(p.ops, Ops) and p.ops.isCond():
			e = p.ops.getCond()
			ops1 = p.ops.__class__(*p.ops.elements)
			ops2 = p.ops.__class__(*p.ops.elements)
			pTrue = p.__class__(ops1, next)
			pFalse = p.__class__(ops2, next)
			realizeCond(pTrue.ops)
			eliminateCond(pFalse.ops)
			tBranch = OpsNode(Assume(e.cond), [pTrue])
			if e.cond == True:
				negCond = False
			else:
				negCond = ~(e.cond)
			fBranch = OpsNode(Assume(negCond), [pFalse])

			p.ops = Ops()
			p.next = [tBranch, fBranch]
			fBranch.pred = fBranch.pred.union(set([p]))
			tBranch.pred = tBranch.pred.union(set([p]))
		for i in next:
			editConditionNode(i)

	editConditionNode(P)
	
	# link it
	def editBranchNode(p, labels):
		assert(isinstance(p, OpsNode))
		next = p.next 
		if isinstance(p.ops, Ops) and p.ops.isBranch():
			b = p.ops.getBranch()
			if labels[str(b.label)].dominates(p):
				p.isLoop = True

			# print labels.keys()[0]
			ops1 = p.ops.clone()
			ops2 = p.ops.clone()
			pTrue = p.__class__(ops1, [labels[str(b.label)]])
			pFalse = p.__class__(ops2, p.next)
			tBranch = OpsNode(Assume(b.cond), [pTrue])
			if b.cond == True:
				negCond = False
			else:
				negCond = ~(b.cond)
			fBranch = OpsNode(Assume(negCond), [pFalse])

			p.ops = Ops()
			p.next = [fBranch, tBranch]
			fBranch.pred = fBranch.pred.union(set([p]))
			tBranch.pred = tBranch.pred.union(set([p]))
		for i in next:
			editBranchNode(i, labels)
	prepareDominators(P)
	editBranchNode(P, labels)


	return P


def unwindLoop(p, inNode, k = 0):
	assert(isinstance(p, OpsNode))
	ret = SeqOps(p.ops)
	if p.isLoopBranch(inNode):
		if k > 0: 	# in bound for loop
			for i in p.next:
				for u in unwindLoop(i, inNode, k-1):
					yield ret + u
		else:		# out bound for loop
			x = p.getConseq(inNode)
			for u in unwindLoop(x, inNode, 0):
				yield ret + u
	else:
		if len(p.next) == 0:
			# print p.ops
			yield ret
		else:
			for i in p.next:
				for u in unwindLoop(i, inNode, k):
					# print p.ops
					yield ret + u
def unrollCombination(P, k = 0):
	def exploreExecution(U):
		if len(U) >= 1:
			E = []
			for u in U[0]:
				
				E += [u]
			for es in exploreExecution(U[1:]):
				for e in E:
					yield [e] + es
		else: 
			yield []

	if not isinstance(P, list):
		P = [P]
	U = []
  	for p in P:
  		# prepare dominator 
  		prepareDominators(p)
  		# for i in p:
  		# 	print i
  		# 	print '----'
  		# return []
  		U += [unwindLoop(p, p, k)]
  	return exploreExecution(U)


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

def mp2():
	P1 = seqOpsNode(
			InstrOps(	# mov r1, #1
				TempReg('val') << 1, 
				Register('r1') << TempReg('val')
				),
			InstrOps(	# str r1, [x]
				TempReg('val') << Register('r1'),
				ParOps(TempReg('val1') << Register('r1'), TempReg('val2') << Register('r1')),
				Location('x') << TempReg('val')
				),
			InstrOps(	# str r1, [y]
				TempReg('val') << Register('r1'),
				Location('y') << TempReg('val'),
				CondOps(TempReg('val') == 1, 
					SeqOps(
						TempReg('val') << Register('r1'),
						Location('y') << TempReg('val')
						)
					)

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

	LabelNode = OpsNode(LabelStm('A'), [])
	BranchNode = OpsNode(
						InstrOps(
							branchOp(Register('r1') == 1, LabelStm('B'))
						),[
							OpsNode(InstrOps(	# str r1, [y]
								TempReg('val') << Register('r1'),
								Location('y') << TempReg('val')
								))
							# TerminateNode()
							# , LabelNode
						])
	# print P1
	P1 << BranchNode
	P1 << OpsNode(LabelStm('B'))
	LabelNode.next = [P1]	
	# print dominate(LabelNode, BranchNode, LabelNode)
		
	print '+++++++'
	
	LabelNode = branchExtractor(LabelNode)
	# U = unwindLoop(LabelNode, LabelNode, 1)
	U = unrollCombination([LabelNode], 0)
	# i = 0
	for p in U:
		# print p
		for i in ssa_form(p):
			print i
		
		print '----'
	# print i
	# for p in P1:
	# 	print p
	# 	print '----'
	pass 

if __name__ == '__main__':
	mp2()
	pass 