from Arch.objects import *


def getAssnVars(p):
	if isinstance(p, Assertion):
		return []
	elif isinstance(p, Assume):
		return []
	elif isinstance(p, Assignment) and not(isinstance(p.var, TempReg)):
		return [p.var]
	elif isinstance(p, ParOps):
		newPar = []
		for i in p.elements:
			newPar += getAssnVars(i)
		return newPar
	elif isinstance(p, OprStoreCond):
		return [p.var]
	# elif isinstance(p, IfStm):
	# 	assnVars = []
	# 	for i in p.list():
	# 		assnVars += getAssnVars(i)
	# 	# print SeqSem(*newSeq)
	# 	return assnVars
	elif isinstance(p, Ops):
		newSeq = []
		for i in p.elements:
			newSeq += getAssnVars(i)
		return newSeq
	elif isinstance(p, OpsNode):
		v = []
		for i in p:
			v += getAssnVars(i)
		return v
	return []

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

def newIndInv(P):
	# Todo: new assertion language 

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

	

	# Todo: expand each P
	def expandProg(P):
		ret = OpsNode(SeqOps())
		for p in P.exploreNodes():
			if isinstance(p.ops, IfBr):
				tBr = invExtractor(seqOpsNode(*(p.ops.t_body.elements)), vars)
				o = seqOpsNode( Assume(p.ops.cond), InstrOps(branchOp(False, LabelStm(''), True)) ) 
				o << tBr
				# fBr = invExtractor(seqOpsNode(*(p.ops.f_body.elements)), vars)
				ifBr = OpsNode(SeqOps(),[
						o,
						seqOpsNode( Assume(~ (p.ops.cond)), InstrOps(branchOp(False, LabelStm(''), True)) )
						# seqOpsNode( Assume(~ (p.ops.cond)), InstrOps(branchOp(False, LabelStm(''), True)) ) + fBr
					])
				ret << ifBr

			elif isinstance(p.ops, SeqOps):
				# i = p
				# i = invExtractor(p, vars)
				# ret << OpsNode(p.ops.clone())
				i = invExtractor(seqOpsNode(*p.ops.elements), vars)
				ret << i
			elif str(p.ops) == 'nil':
				ret << OpsNode(p.ops.clone())
			else:
				# print p.ops, p.ops.__class__
				ret << OpsNode(p.ops.clone())
		return ret

	# Very complicate 
	# for i in range(0, len(P)):
	# 	P[i] = expandProg(P[i])
	# 	editConditionNode(P[i])


	# Todo: count R form each P (worst case)
	def countR(P, infoR = {}):
		for p in P.exploreNodes():
			# print 'hey', p.ops
			if isinstance(p.ops, SeqOps):
				infoR = countR(seqOpsNode(*p.ops.elements), infoR)
			elif isinstance(p.ops, IfBr):
				infoR = countR(seqOpsNode(*p.ops.t_body.elements), infoR)
			elif isinstance(p.ops, CondOps):
				infoR = countR(seqOpsNode(*p.ops.elements), infoR)
			elif isinstance(p.ops, DoWhile):
				infoR = countR(seqOpsNode(*p.ops.body.elements), infoR)
			elif isinstance(p.ops, InstrOps):
				infoR = countR(seqOpsNode(*p.ops.elements), infoR)
			elif isinstance(p.ops, ReadAssn) and isinstance(p.ops.exp, Location):
				if not( str(p.ops.exp) in infoR.keys()):
					infoR[str(p.ops.exp)] = 0
				infoR[str(p.ops.exp)] += 1
			elif isinstance(p.ops, OprLoadLink):
				if not( str(p.ops.loc) in infoR.keys()):
					infoR[str(p.ops.loc)] = 0
				infoR[str(p.ops.loc)] += 1	
		return infoR 


	# > how to save info ?
	info = []
	for i in range(0, len(P)):
		info += [countR(P[i], {})]
		print info[i]
	
	# Todo: invExtract with R info 

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

	# editConditionNode(P)

	def collectLoc(P, s = set([])):
		for p in P.exploreNodes():
			if isinstance(p.ops, DoWhile):
				pass
				print 'not support yet'

			elif isinstance(p.ops, WriteAssn) and isinstance(p.ops.var, Location):
				# ret << OpsNode(p.ops.clone())
				s = s.union([p.ops.var])
			elif isinstance(p.ops, OprStoreCond):
				s =  s.union([p.ops.loc])
			elif isinstance(p.ops, IfBr):
				# for e in p.ops.t_body.elements:
				# 	s = s.union(seqOpsNode(collectLoc(e)))					

				s = s.union(collectLoc(seqOpsNode(*(p.ops.t_body.elements))))
			elif isinstance(p.ops, CondOps):
				# for e in p.ops.elements:
				# 	s = s.union(seqOpsNode(collectLoc(e)))
				s = s.union(collectLoc(seqOpsNode(*p.ops.elements)))
			elif isinstance(p.ops, SeqOps) or isinstance(p.ops, ParOps) or isinstance(p.ops, InstrOps):
				# for e in p.ops.elements:
				# 	s = s.union(seqOpsNode(collectLoc(e)))
				# if(len(p.ops.elements) > 0):
				s = s.union(collectLoc(seqOpsNode(*p.ops.elements)))
			# else:
			# 	print p.ops, p.ops.__class__
		return s 


	def realizeW(P):
		ret = OpsNode(SeqOps())
		for p in P.exploreNodes():
			# print p.ops, p.ops.__class__
			if isinstance(p.ops, DoWhile):
				pass
				print 'not support yet'
				# assert(False)
			elif isinstance(p.ops, WriteAssn) and isinstance(p.ops.var, Location):
				# ret << OpsNode(p.ops.clone())
				ret << (seqOpsNode(havocW(p.ops.var)))
			elif isinstance(p.ops, OprStoreCond):
				# over-approximation approach
				# print p.ops, p.ops.__class__
				writeSuc =  seqOpsNode( havocW(p.ops.loc) , Assignment(p.ops.var, 0) )
				writeFail = seqOpsNode( Assignment(p.ops.var, 1) )
				ret << OpsNode(SeqOps(), [writeSuc, writeFail])
			elif isinstance(p.ops, IfBr):
				tBr = realizeW(seqOpsNode(*(p.ops.t_body.elements)))
				o = OpsNode(SeqOps())
				o << tBr
				ifBr = OpsNode( SeqOps(),[
						o,
						OpsNode(SeqOps())
					])
				ret << ifBr

			# elif isinstance(p.ops, CondOps):
			# 	tBr = realizeW(seqOpsNode(*(p.ops.t_body.elements)))
			# 	o = OpsNode(SeqOps())
			# 	o << tBr
			# 	ifBr = OpsNode( SeqOps(),[
			# 			o,
			# 			OpsNode(SeqOps())
			# 		])
			# 	ret << ifBr
			elif isinstance(p.ops, CondOps):
				e = p.ops.getCond()
				# print p.ops, p.ops.__class__
				ops1 = realizeW(seqOpsNode(*p.ops.elements))
				ops2 = realizeW(seqOpsNode(p.ops.else_element))
				ret << OpsNode( SeqOps(),[
						ops1,
						ops2
					])
			elif isinstance(p.ops, SeqOps) or isinstance(p.ops, ParOps) or isinstance(p.ops, InstrOps):
				# print p.ops, p.ops.__class__
				ret << realizeW(seqOpsNode(*p.ops.elements))


		return ret

	def indInvExtract(P, info):
		
		def arb_w(info):
			return 0

		ret = OpsNode(SeqOps())
		for p in P.exploreNodes():
			if isinstance(p.ops, DoWhile):
				# 'do-while'
				# not support nested loop, yet
				# loopBody = seqOpsNode(*(p.ops.body.elements))


				# arbitrary write 
				locs = collectLoc(seqOpsNode(*(p.ops.body.elements)))

				loopBody = indInvExtract(seqOpsNode(*(p.ops.body.elements)), info)

				# for e in loopBody.exploreNodes():
				# 	print e.ops 
				# print '-----'
				# 
				# loopBody = seqOpsNode(*p.ops.body.elements)
				# print loopBody.ops, loopBody.__class__
				# invExtractor(p.body, vars, p.body.__class__)

				# arbitrary variables
				vars = getAssnVars(loopBody)
				vars = list(set(vars))
				# for v in vars:
				# 	print v

				kWrite = 0
				for l in locs:
					if( str(l) in info.keys()):
						kWrite += info[str(l)]
				print 'kWrite: ', kWrite

				arb_w = OpsNode(SeqOps())
				for i in range(0, kWrite):
					W = realizeW(loopBody.copy())
					# # print 'w', W
					# arb_w << W
					# print '====w '
					# for w in W.exploreNodes():
					# 	print w.ops
					arb_w << W
					arb_w << seqOpsNode(Assume(p.ops.inv))
					# add inv ?
					# arb_w << realizeW(loopBody.clone()) 
				loopBody1 = seqOpsNode( Assume(~(p.ops.bInstr)), InstrOps(
							branchOp(False, LabelStm(''), True)
							))
				loopBody2 = seqOpsNode(
					Assume((p.ops.bInstr)),
					Assertion(p.ops.inv),
					InstrOps(
						branchOp(False, LabelStm(''), True) 	# there is a branch operation appear
					),
					havoc(*([] + vars)))
				loopBody2 << arb_w
				loopBody2 << seqOpsNode(
					Assume(p.ops.inv),
					Assume(p.ops.bInstr),
					InstrOps(
						branchOp(False, LabelStm(''), True) 	# there is a branch operation appear
					),
					)
				elseBranch = seqOpsNode( Assume(~(p.ops.bInstr)), InstrOps(
							branchOp(False, LabelStm(''), True)
							))
				loopBody2 << loopBody.copy()
				loopBody2 << OpsNode(SeqOps(), [
							elseBranch, 
						OpsNode( Assertion(p.ops.inv), [TerminateNode()] )
					])
				# ret << loopBody2
				# emptyNode = OpsNode(Assertion(p.ops.inv))
				# emptyNode.pred = emptyNode.pred.union(set([ret]))
				# ret.next += [emptyNode]
				# print ret.next,OpsNode(SeqOps()) 
				# ret << OpsNode(SeqOps())
				loopBody << OpsNode(SeqOps(), [
						loopBody1,
						loopBody2,
						# OpsNode(SeqOps()),
						
						])
				ret << loopBody
			elif isinstance(p.ops, IfBr):
				tBr = indInvExtract(seqOpsNode(*(p.ops.t_body.elements)), info)
				# tBr = indInvExtract(seqOpsNode(*(p.ops.t_body.elements)), vars)
				# tBr = invExtractor(seqOpsNode(*(p.ops.t_body.elements)), vars)
				o = seqOpsNode( Assume(p.ops.cond), InstrOps(branchOp(False, LabelStm(''), True)) ) 
				o << tBr
				# fBr = invExtractor(seqOpsNode(*(p.ops.f_body.elements)), vars)
				ifBr = OpsNode(SeqOps(),[
						o,
						seqOpsNode( Assume(~ (p.ops.cond)), InstrOps(branchOp(False, LabelStm(''), True)) )
						# seqOpsNode( Assume(~ (p.ops.cond)), InstrOps(branchOp(False, LabelStm(''), True)) ) + fBr
					])
				ret << ifBr
			elif isinstance(p.ops, SeqOps):
				# i = p
				# i = invExtractor(p, vars)
				# ret << OpsNode(p.ops.clone())
				i = invExtractor(seqOpsNode(*p.ops.elements), vars)
				ret << i
			elif isinstance(p.ops,Operation):
				ret << OpsNode(p.ops.clone())

			elif isinstance(p.ops,AnnotatedStatement):
				# print OpsNode(p.ops.clone()).ops
				
				ret << OpsNode(p.ops.clone())
			elif isinstance(p.ops, InstrOps):

				ret << OpsNode(p.ops.clone())
				# print 'ret'
				# for e in ret:
				# 	print e 
			else:
				print p.ops, p.ops.__class__
				assert(False)
		return ret

	all_info = {}
	for i in range(0, len(P)):
		for l in info[i].keys():
			if not( l in all_info.keys() ):
				all_info[l] = 0	
			all_info[l] += info[i][l]

	for i in range(0, len(P)):
		
		# # B = P[i].clone() 
		# arb_w =  OpsNode(SeqOps())
		# arb_w << realizeW(P[i].clone())
		# arb_w << seqOpsNode(Assume(True))
		# arb_w << realizeW(P[i].clone())
		# arb_w << seqOpsNode(Assume(True))
		# # B = realizeW(B)
		# # A << B
		# P[i] = arb_w

		info_i = all_info.copy()
		for l in info[i].keys():
			info_i[l] -= info[i][l]
		print info_i
		P[i] = indInvExtract(P[i], info_i)
	return P

def invExtractor(P, vars = []):
	# no goto inside do-while !!

	# vars = locations + local registers
	ret = OpsNode(SeqOps())
	# ret = emptyCS()

	for p in P.exploreNodes():
		if isinstance(p.ops, DoWhile):
			# 'do-while'
			loopBody = seqOpsNode(*(p.ops.body.elements))
			# loopBody = invExtractor(seqOpsNode(*(p.ops.body.elements)), vars)

			# for e in loopBody.exploreNodes():
			# 	print e.ops 
			# print '-----'
			# 
			# loopBody = seqOpsNode(*p.ops.body.elements)
			# print loopBody.ops, loopBody.__class__
			# invExtractor(p.body, vars, p.body.__class__)
			vars = getAssnVars(loopBody)
			vars = list(set(vars))
			# for v in vars:
			# 	print v

			loopBody1 = seqOpsNode( Assume(~(p.ops.bInstr)), InstrOps(
						branchOp(False, LabelStm(''), True)
						))
			loopBody2 = seqOpsNode(
				Assertion(p.ops.inv),
				InstrOps(
					branchOp(False, LabelStm(''), True) 	# there is a branch operation appear
				),
				havoc(*([] + vars)),
				Assume(p.ops.inv),
				Assume(p.ops.bInstr),
				InstrOps(
					branchOp(False, LabelStm(''), True) 	# there is a branch operation appear
				),
				)
			elseBranch = seqOpsNode( Assume(~(p.ops.bInstr)), InstrOps(
						branchOp(False, LabelStm(''), True)
						))
			loopBody2 << loopBody.copy()
			loopBody2 << OpsNode(SeqOps(), [
						elseBranch, 
					OpsNode( Assertion(p.ops.inv), [TerminateNode()] )
				])
			# ret << loopBody2
			# emptyNode = OpsNode(Assertion(p.ops.inv))
			# emptyNode.pred = emptyNode.pred.union(set([ret]))
			# ret.next += [emptyNode]
			# print ret.next,OpsNode(SeqOps()) 
			# ret << OpsNode(SeqOps())
			loopBody << OpsNode(SeqOps(), [
					loopBody1,
					loopBody2,
					# OpsNode(SeqOps()),
					
					])
			ret << loopBody
		elif isinstance(p.ops, IfBr):
			tBr = invExtractor(seqOpsNode(*(p.ops.t_body.elements)), vars)
			o = seqOpsNode( Assume(p.ops.cond), InstrOps(branchOp(False, LabelStm(''), True)) ) 
			o << tBr
			# fBr = invExtractor(seqOpsNode(*(p.ops.f_body.elements)), vars)
			ifBr = OpsNode(SeqOps(),[
					o,
					seqOpsNode( Assume(~ (p.ops.cond)), InstrOps(branchOp(False, LabelStm(''), True)) )
					# seqOpsNode( Assume(~ (p.ops.cond)), InstrOps(branchOp(False, LabelStm(''), True)) ) + fBr
				])
			ret << ifBr
		elif isinstance(p.ops, SeqOps):
			# i = p
			# i = invExtractor(p, vars)
			# ret << OpsNode(p.ops.clone())
			i = invExtractor(seqOpsNode(*p.ops.elements), vars)
			ret << i
		elif isinstance(p.ops,Operation):
			ret << OpsNode(p.ops.clone())

		elif isinstance(p.ops,AnnotatedStatement):
			# print OpsNode(p.ops.clone()).ops
			
			ret << OpsNode(p.ops.clone())
		elif isinstance(p.ops, InstrOps):

			ret << OpsNode(p.ops.clone())
			# print 'ret'
			# for e in ret:
			# 	print e 
		else:
			print p.ops, p.ops.__class__
			assert(False)
	# ret << P
	# for p in P.exploreNodes():
	# 	print p, p.pred

	return ret

def prepareDominators(p):
	nodes = set([i for i in p.exploreNodes()])
	rNodes = nodes - set([p])
	# print p

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
			# print i, i.next
			# if len(i.next) > 0:
			# 	print i.next[0].ops
			ret = exploreLabel(i, ret)

		# for a in p.exploreNodes():
		# 	if isinstance(p.ops, LabelStm):
		# 	ret[str(p.ops)] = p

		return ret 
	labels = exploreLabel(P)
	# print labels


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

		if isinstance(p.ops, Ops) and p.ops.isBranch() and not hasattr(p, 'modified') and not p.ops.getBranch().fake_op:

			b = p.ops.getBranch()
			# print b
			if labels[str(b.label)].dominates(p):
				p.isLoop = True
			# print labels[str(b.label)],p,p.isLoop

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
	# print P
	U = []
  	for p in P:
  		# prepare dominator 
  		prepareDominators(p)
  		# print 'dom'
  		# for i in p:
  		# 	print i
  		# 	print '----'
  		# # return []
  		U += [unwindLoop(p, p, k)]
  	return exploreExecution(U)

pathExploring = unrollCombination
