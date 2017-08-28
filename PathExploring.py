from Arch.objects import *


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

def GraphPreparation(P):
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
				cond = p.elements[i].cond
				p.elements[i] = p.elements[i].else_element
				p.elements.insert(i, Assume(~cond))
			elif isinstance(p.elements[i], Ops):
				eliminateCond(p.elements[i])

	def realizeCond(p):
		assert(isinstance(p, Ops))
		for i in range(0, len(p.elements)):
			if isinstance(p.elements[i], CondOps):
				# print 'realize',p.elements[i].elements[0] 
				cond = p.elements[i].cond
				p.elements[i] = p.elements[i].elements[0]
				p.elements.insert(i, Assume(cond))
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


			# if (isinstance(e.cond,bool) and e.cond == True):
			# 	negCond = False
			# else:
			# 	negCond = ~(e.cond)

			realizeCond(pTrue.ops)
			eliminateCond(pFalse.ops)
			# tBranch = OpsNode(Assume(e.cond), [pTrue])
			# fBranch = OpsNode(Assume(negCond), [pFalse])
			tBranch = pTrue
			fBranch = pFalse

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

		if hasattr(p, 'modified'):
			return 

		if isinstance(p.ops, Ops) and p.ops.isBranch() and not hasattr(p, 'modified'):

			b = p.ops.getBranch()
			if labels[str(b.label)].dominates(p):
				p.isLoop = True

			# print labels.keys()[0]
			ops1 = p.ops.clone()
			ops2 = p.ops.clone()
			pTrue = p.__class__(ops1, [labels[str(b.label)]])

			# modify ops2 for SPARC arch
			ops2 = InstrOps(branchOp(b.cond, b.label))

			pFalse = p.__class__(ops2, p.next)

			if p.isLoop:
				pTrue.modified = True
				pFalse.modified = True

			tBranch = OpsNode(Assume(b.cond), [pTrue])
			if (isinstance(b.cond,bool) and b.cond == True):
				negCond = False
				# fBranch = TerminateNode()
				# fBranch = OpsNode(Assume(negCond), [TerminateNode()])
				fBranch = OpsNode(Assume(negCond), [TerminateNode()])
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

pathExploring = unrollCombination
