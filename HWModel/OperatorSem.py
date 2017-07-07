# Semantics of operations 

from z3 import *
import itertools

from annotation import *
from sets import Set


# ----------------- Operations
# class Operation(AnnotatedStatement):
class Operation():
	def __init__(self):
		pass 
	def clone(self):
		return self.__class__()

# <var> := <exp>
# <var> ::= <reg> | <loc> | <symbolic var>
class Assignment(Operation):
	def __init__(self, var, exp):
		self.var = var
		self.exp = exp
	def clone(self):
		return self.__class__(self.var.clone(), self.exp)

	def __str__(self):
		return str(self.var) + " := " + str(self.exp) + ' (' + str(self.__class__) + ')' 

# <loc> := <val> {symbolic / concrete}
class WriteAssn(Assignment):
	pass 

# <reg> := <val> {symbolic / concrete}
class ReadAssn(Assignment):
	pass 

class Reserve(Operation):
	def __init__(self, location):
		self.location = location 
	def clone(self):
		return self.__class__(self.location)
	def __str__(self):
		return 'reserve(' + str(self.location) + ')'

# fence()
class fenceStm(Operation):
	def __init__(self):
		pass
	def clone(self):
		return self.__class__()
	def __str__(self):
		return 'fence()' 
		
class branchOp(Operation):
	def __init__(self, cond, label):
		self.cond = cond
		self.label = label
	def clone(self):
		return self.__class__(self.cond, self.label)
	def __str__(self):
		return 'branch(' + str(self.cond) + ', ' + str(self.label) + ')'

# ---------------- Execution on operations
# sequential execution -> list ?
# parallel execution -> tuple ?
# CodeBlock used for:
# > do-while execution - loop
# > if-branch execution - condition 

class SeqSem:
	def __init__(self, *seq):
		# print type(seq)
		self.seq = list(seq)
		for i in self.seq:
			assert( isinstance(i, Operation) or isinstance(i, AnnotatedStatement) or isinstance(i, SeqSem) )

	def __iter__(self):
		for i in self.seq:
			if isinstance(i, SeqSem):
				for p in i:
					yield p
			else: 
				yield i
	def list(self):
		return list(self.seq)

	def strIndent(self, indent = 0):
		ret = ''
		ret += (' '* indent) + 'seq[ \n'
		for i in self.seq:
			iStr = ''
			if isinstance(i, SeqSem):
				iStr = i.strIndent(indent + 1)
			else:
				iStr = (' '*(indent+1)) +str(i)
			ret += (' '* indent) + iStr + ',\n'
		ret += (' '* indent) + ']'
		return ret

	def __str__(self):
		return self.strIndent()

	def __lshift__(self, other):
		clss = self.__class__
		assert(isinstance(other, Operation) or isinstance(other, Assertion) or isinstance(other, Assume) or isinstance(other, SeqSem))

		if isinstance(self, IfStm):
			self.sem += [other]
		elif isinstance(self, ParallelSem):
			self.par += [other]
		else:
			self.seq += [other]

		# if isinstance(other, SeqSem):
		# 	if isinstance(other, ParallelSem) or isinstance(other, InstrSem) or isinstance(other, IfStm):
		# 		seq = seq + [other]
		# 		# clss = other.__class__
		# 	elif isinstance(self, ParallelSem) or isinstance(self, InstrSem) or isinstance(self, IfStm):
		# 		clss = SeqSem
		# 		seq = [self.__class__(*seq),other]
		# 	else:
		# 		seq = seq + other.seq
		# else:
		# 	seq = seq + [other]
		# return clss(*seq)

	def __add__(self, other):
		clss = self.__class__
		assert(isinstance(other, Operation) or isinstance(other, Assertion) or isinstance(other, Assume) or isinstance(other, SeqSem))

		if isinstance(self, IfStm):
			seq = self.sem
		elif isinstance(self, ParallelSem):
			seq = self.par
		else:
			seq = self.seq

		if isinstance(other, SeqSem):
			if isinstance(other, ParallelSem) or isinstance(other, InstrSem) or isinstance(other, IfStm):
				seq = seq + [other]
				# clss = other.__class__
			elif isinstance(self, ParallelSem) or isinstance(self, InstrSem) or isinstance(self, IfStm):
				clss = SeqSem
				seq = [self.__class__(*seq),other]
			else:
				seq = seq + other.seq
		else:
			seq = seq + [other]
		return clss(*seq)
		

class ParallelSem(SeqSem):
	# assume that no loop in Parallel Sem
	def __init__(self, *par):
		self.par = list(par)
		for i in self.par:
			assert( isinstance(i, Operation) or isinstance(i, AnnotatedStatement) or isinstance(i, SeqSem) )
			assert( not isinstance(i, DoWhile))
		# self.seq = self.par

	def __iter__(self):
		for i in self.par:
			if isinstance(i, SeqSem):
				for p in i:
					yield p
			else: 
				yield i
	def list(self):
		return list(self.par)

	def strIndent(self, indent = 0):
		ret = ''
		ret += (' '* indent) + 'parallel( \n'
		for i in self.par:
			iStr = ''
			if isinstance(i, SeqSem):
				iStr = i.strIndent(indent + 1)
			else:
				iStr = (' '*(indent+1)) +str(i)
			ret += (' '* (indent)) + iStr + ', \n'
		ret += (' '* indent) + ')'
		return ret

	def __str__(self):
		return self.strIndent()

class InstrSem(SeqSem):
	def strIndent(self, indent = 0):
		ret = ''
		ret += (' '* indent) + 'instr[ \n'
		for i in self.seq:
			iStr = ''
			if isinstance(i, SeqSem):
				iStr = i.strIndent(indent + 1)
			else:
				iStr = (' '*(indent+1)) +str(i)
			ret += (' '* indent) + iStr + ',\n'
		ret += (' '* indent) + ']'
		return ret

# if(cond) {SeqSem}
class IfStm(SeqSem):
	def __init__(self, cond, *sem):
		self.cond = cond
		self.sem = list(sem)
		self.isBranch = True
	def isBranch(self, v):
		self.isBranch = v

	def strIndent(self, indent = 0):
		ret = ''
		ret += (' '* indent) + 'if(%s)[ \n'%str(self.cond)
		for i in self.sem:
			iStr = ''
			if isinstance(i, SeqSem):
				iStr = i.strIndent(indent + 1)
			else:
				iStr = (' '*(indent+1)) +str(i)
			ret += (' '* indent) + iStr + ',\n'
		ret += (' '* indent) + ']'
		return ret

	def list(self):
		return list(self.sem)

# rmw{ ... } accepts only operations
# requires the operations APPEAR as an atomic execution
class RmwStm(SeqSem):
	def __init__(self, r, w):
		assert(isinstance(r, ReadAssn) and isinstance(w, WriteAssn))
		self.seq = [r,w]
		for i in self.seq:
			assert( isinstance(i, Operation) )

	def strIndent(self, indent = 0):
		ret = ''
		ret += (' '* indent) + 'rmw{ \n'
		for i in self.seq:
			iStr = ''
			if isinstance(i, SeqSem):
				iStr = i.strIndent(indent + 1)
			else:
				iStr = (' '*(indent+1)) +str(i)
			ret += (' '* indent) + iStr + ',\n'
		ret += (' '* indent) + '}'
		return ret

	def __lshift__(self, other):
		clss = self.__class__
		assert(isinstance(other, Operation))
		self.seq += [other]

	def __add__(self, other):
		clss = self.__class__
		assert(isinstance(other, Operation))
		seq = self.seq
		seq = seq + [other]
		return clss(*seq)

# --------- Code Structure
class CodeStructure():
	def __init__(self, seq, next = []):		
		self.body = seq
		self.next = next
		

	def body(self):
		return self.body

	def __iter__(self):
		if len(self.next) == 0:
			yield self.body
		else:
			for i in self.next:
				# print self
				# print i
				# print '-----debug'
				# print i.body
				# print '-----debug----'
				for p in i:
					yield self.body + p
	def __getitem__(self, key):
		return SeqSem(self.body, self.next[key].getSem())
	def getSem(self, key = 0):
		if self.next:
			return self.body + self.next[key].getSem()
		return self.body
	def addMergePoint(self, other):

		if self == other:
			return 
			# assert(False)
		if self.next == []:
			self.next = [other]
		else:
			for n in self.next:
				if not isinstance(n, terminateCS):
					n.addMergePoint(other)

	def __lshift__(self, other):
		assert(isinstance(other, Operation) or isinstance(other, AnnotatedStatement) or isinstance(other, SeqSem) or 
			isinstance(other, CodeStructure))
		body = self.body
		next = self.next[:]
		if isinstance(other, CodeStructure):
			if next == []:
				# print 'self.', self.body.__class__
				# print other.next
				self.body << other.body
				self.next = other.next
				# self.next = [other]
			else:
				# a = self.next[0]
				# print self.next[0]
				# a << other
				# print a
				# print self.next[0]
				self.next[0] << other
				

				# for i in self.next:
				# 	i += other
		elif next == []:
			self.body += other
		else: 
			self.next[0] << other

	def __add__(self, other):

		assert(isinstance(other, Operation) or isinstance(other, AnnotatedStatement) or isinstance(other, SeqSem) or 
			isinstance(other, CodeStructure))
		body = self.body
		next = self.next[:]

		if isinstance(other, CodeStructure):
			if next == []:
				body = body + other.body
				next = other.next
			else:
				next[0] = next[0] + other
		elif next == []:
			body = body + other
			# next[0] = next[0] + other
		else: 
			next[0] = next[0] + other

		return CodeStructure(body, next)
		# if isinstance(other, Operation):
		# 	self.next[0] += other 
		# elif isinstance(other, SeqSem):
		# 	self.next[0] = SeqSem(self.next[0] + other)
		# else:

# idM = 0
class mergePointCS(CodeStructure):
	def __init__(self):		
		# global idM
		# self.id = idM
		# idM += 1
		self.body = SeqSem()
		self.next = []
		

	def body(self):
		return SeqSem()

	# def __iter__(self):
	# 	yield SeqSem()

	# def __getitem__(self, key):
	# 	return SeqSem()
	# def __str__(self):
	# 	return 'merge point'

	def __lshift__(self, other):
		# print 'lshift merge'
		# print 'other', other
		if self.next == []:
			if isinstance(other, CodeStructure):
				# body = other.body
				# print 'CS'
				self.next = [other]
			else: 
				# print other.__class__
				self.next = [CodeStructure(SeqSem(other), [])]
		else:
			self.next[0] += other
		# print other.__class__
		# for u in self:
		# 	print u
		# print 'xxxxxxxx'

	def __add__(self, other):
		# print 'add merge'
		assert(isinstance(other, Operation) or isinstance(other, AnnotatedStatement) or isinstance(other, SeqSem) or 
			isinstance(other, CodeStructure))

		next = self.next[:]
		if self.next == []:
			if isinstance(other, CodeStructure):
				# body = other.body
				# print 'CS'
				next = [other]
			else: 
				# print other.__class__
				next = [CodeStructure(SeqSem(other), [])]
		else:
			# for u in self:
			# 	print u
			# print next[0], other
			# assert(False)
			next[0] << other

		return CodeStructure(self.body, next)

class terminateCS(CodeStructure):
	def __init__(self):
		self.body = SeqSem()
		self.next = []

class emptyCS(CodeStructure):
	def __init__(self):		
		pass
		

	def body(self):
		return SeqSem()

	def __iter__(self):
		yield SeqSem()

	def __getitem__(self, key):
		return SeqSem()

	def __lshift__(self, other):
		self = other 

	def __add__(self, other):

		assert(isinstance(other, Operation) or isinstance(other, AnnotatedStatement) or isinstance(other, SeqSem) or 
			isinstance(other, CodeStructure))
	
		next = []
		if isinstance(other, CodeStructure):
			body = other.body
			next = other.next
		else: 
			body = SeqSem(other)

		return CodeStructure(body, next)
		# if isinstance(other, Operation):
		# 	self.next[0] += other 
		# elif isinstance(other, SeqSem):
		# 	self.next[0] = SeqSem(self.next[0] + other)
		# else:

# Definition of Operation Structure
class Ops:
	# nothing
	def __init__(self):
		self.elements = []

	def clone(self):
		return self.__class__()
		
	def strIndent(self, indent = 0):
		ret = (' '* indent) + 'emptyOps'
		return ret

	def __str__(self):
		return self.strIndent()

	def isBranch(self):
		for e in self.elements:

			if isinstance(e, branchOp):
				return True
			elif isinstance(e, Ops):
				if e.isBranch():
					return True
		return False 
	def getBranch(self):
		for e in self.elements:
			if isinstance(e, branchOp):
				return e
			elif isinstance(e, Ops):
				return e.getBranch()
		return None
	 
	def isCond(self):
		for e in self.elements:
			if isinstance(e, CondOps):
				return True
			elif isinstance(e, Ops):
				if e.isCond():
					return True
		return False 

	def getCond(self):
		for e in self.elements:
			if isinstance(e, CondOps):
				return e
			elif isinstance(e, Ops):
				return e.getCond()
		return None

class SeqOps(Ops):
	def __init__(self, *seq):
		self.elements = list(seq)
	def clone(self):
		new_elements = []
		for e in self.elements:
			new_elements += [e.clone()]
		return self.__class__(*new_elements)
	def append(self, other):
		if isinstance(other, SeqOps):
			self.elements += other.elements
		elif isinstance(other, Ops) and other.elements == []:
			pass
		else:
			self.elements += [other]
	def __add__(self, other):
		if isinstance(other, SeqOps):
			elements = self.elements + other.elements
			return SeqOps(*elements)
		elif isinstance(other, Ops):
			elements = self.elements + [other]
			return SeqOps(*elements)
		elif isinstance(other, AnnotatedStatement):
			elements = self.elements + [other]
			return SeqOps(*elements)
		else:
			print other.__class__
			assert(False)
	def strIndent(self, indent = 0):
		ret = ''
		ret += (' '* indent) + 'seq[ \n'
		for i in self.elements:
			iStr = ''
			if isinstance(i, Ops):
				iStr = i.strIndent(indent + 1)
			else:
				iStr = (' '*(indent+1)) +str(i)
			ret += (' '* indent) + iStr + ',\n'
		ret += (' '* indent) + ']'
		return ret

	def __str__(self):
		return self.strIndent()


class ParOps(Ops):
	def __init__(self, *seq):
		self.elements = list(seq)
	def clone(self):
		new_elements = []
		for e in self.elements:
			new_elements += [e.clone()]
		return self.__class__(*new_elements)
	def append(self, other):
		self.elements += [other]
	def __add__(self, other):
		if isinstance(other, Ops):
			elements = [self] + [other]
			return SeqOps(*elements)
		else:
			assert(False)
	def strIndent(self, indent = 0):
		ret = ''
		ret += (' '* indent) + 'par[ \n'
		for i in self.elements:
			iStr = ''
			if isinstance(i, Ops):
				iStr = i.strIndent(indent + 1)
			else:
				iStr = (' '*(indent+1)) +str(i)
			ret += (' '* indent) + iStr + ',\n'
		ret += (' '* indent) + ']'
		return ret

	def __str__(self):
		return self.strIndent()
class InstrOps(Ops):
	def __init__(self, *seq):
		self.elements = list(seq)
	def clone(self):
		new_elements = []
		for e in self.elements:
			new_elements += [e.clone()]
		return self.__class__(*new_elements)
	def append(self, other):
		if isinstance(other, SeqOps):
			self.elements += other.elements
		elif isinstance(other, Operation):
			self.elements += [other]
		elif isinstance(other, ParOps):
			self.elements += [other]
		elif isinstance(other, InstrOps):
			self.elements += [other]
		elif isinstance(other, Atomic):
			# assert(False)
			self.elements += [other]
		elif isinstance(other, Ops):
			# self.elements += []
			pass
		else:
			print other
			assert(False)
			self.elements += [other]


	def __add__(self, other):
		if isinstance(other, Ops):
			elements = [self] + [other]
			return SeqOps(*elements)
		elif isinstance(other, AnnotatedStatement):
			elements = [self] + [other]
			return SeqOps(*elements)
		else:
			print other 
			assert(False)
	def strIndent(self, indent = 0):
		ret = ''
		ret += (' '* indent) + 'instr[' + ' \n' 
		for i in self.elements:
			iStr = ''
			if isinstance(i, Ops):
				iStr = i.strIndent(indent + 1)
			else:
				iStr = (' '*(indent+1)) +str(i)
			ret += (' '* indent) + iStr + ',\n'
		ret += (' '* indent) + ']'
		return ret

	def __str__(self):
		return self.strIndent()

class CondOps(Ops):
	def __init__(self, cond, s, s2 = Ops()):
		self.cond = cond
		self.elements = [s]
		self.else_element = s2
	def clone(self):

		return self.__class__(self.cond, self.elements[0].clone())
	def append(self, other):
		self.elements += other 
	def __add__(self, other):
		if isinstance(other, Ops):
			elements = [self] + [other]
			return SeqOps(*elements)
		else:
			assert(False)		

	def strIndent(self, indent = 0):
		ret = ''
		ret += (' '* indent) + 'if('+ str(self.cond) +')[ \n'
		for i in self.elements:
			iStr = ''
			if isinstance(i, Ops):
				iStr = i.strIndent(indent + 1)
			else:
				iStr = (' '*(indent+1)) +str(i)
			ret += (' '* indent) + iStr + ',\n'
		ret += (' '* indent) + ']'
		return ret

	def __str__(self):
		return self.strIndent()



def dominate(inNode, u, v):
	return inNode.reach(u) and inNode.reach(v) and u.reach(v)

def seqOpsNode(*seq):
	seq = list(seq)
	prev = []
	for i in range(len(seq)-1, -1, -1):

		e = OpsNode(seq[i], prev)
		prev = [e]
	return e

class OpsNode:


	def __init__(self, ops, next = []):
		# print ops.__class__
		assert(isinstance(ops, InstrOps) or isinstance(ops, AnnotatedStatement))
		self.ops = ops 
		self.next = next 
		self.isLoop = False

		self.dominator = set([])

		self.pred = set([])
		for i in next:

			i.pred = i.pred.union(set([self]))
			# print i.pred

		# self.reachList = Set([self])
		# for i in next:
		# 	# print 'beforeAdd',self.reachList, i.reachList
		# 	self.reachList.add(i.reachList)
			# print 'afterAdd',self.reachList
		# print self.reachList 

	def __lshift__(self, other):
		if self.next == []:
			self.next = [other]
		else:
			for i in self.next:
				i << other 

	def __add__(self, other):
		ops = self.ops 
		next = self.next[:]
		if next == []:
			next = [other]
		else:
			n = len(next)
			for i in range(0, n):
				next[i] = next[i] + other 
		return OpsNode(ops, next)
	def __iter__(self):
		ret = SeqOps(self.ops)

		if self.next == []:
			yield ret
		for i in self.next:
			if len(self.next) > 1:
				yield ret + i.ops
			else:
				for p in i:
					yield ret + p

	def exploreNodes(self, visited = []):
		if not ( self in visited ):
			yield self
			for i in self.next:
				for p in i.exploreNodes(visited + [self]):
					yield p

	def dominates(self, other):
		if self.dominator == set([]):
			assert(False)
		return self in other.dominator


	def reach(self, other, tmp = []):
		# Is this terminate ?
		assert(isinstance(other, OpsNode))
		# print tmp
		if other.ops in self.reachList:
			return True
		return False

		for i in self.next:
			if i.reach(other):
				self.reachList.union(i.reachList)	
				return True 
					

			# self.reachList = list(set(self.reachList))

			# if not(i in tmp) and i.reach(other, tmp + [self]):
			# 	return True
		return False 

	def getConseq(self, inNode):
		assert(len(self.next) > 0)
		for i in self.next:
			# if not dominate(inNode, i, self):
			if not(i.dominates(self)):
				return i
		assert(False)
		return self.next[0]

	def isLoopBranch(self, inNode):
		if isinstance(self.ops, Ops) and len(self.next) > 1:
			# return True
			return self.isLoop
		# 	for i in self.next:
		# 		# if dominate(inNode, i, self):
		# 		# print i.ops, i.dominates(self)
		# 		# print '-----'
		# 		# for d in i.dominator:
		# 		# 	print d.ops
		# 		# print '00000'
		# 		if i.dominates(self):
		# 			return True 
		# 	assert(False)
		return False

class TerminateNode(OpsNode):
	def __init__(self):
		self.ops = Ops()
		self.next = []
		self.isLoop = False

		self.dominator = set([])

		self.pred = set([])
	def __lshift__(self, other):
		return self
	def __add__(self, other):
		return self
	def __iter__(self):
		yield Ops()

if __name__ == '__main__':
	print 'hello operation structure'

	P1 = InstrOps('0')
	P1.append( 
		SeqOps(
		'A',
		ParOps('B', 'C'),
		CondOps('cond1',
			SeqOps(
				'D',
				'E'
				)
			)
		))
	print P1








