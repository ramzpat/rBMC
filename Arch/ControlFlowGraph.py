from OperationStructure import *
from Annotation import *

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
		assert(isinstance(ops, SeqOps) or isinstance(ops, InstrOps) or isinstance(ops, AnnotatedStatement))
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
	def clone(self):
		newNext = self.next[:]
		# for e in self.next:
		# 	newNext += [e.clone()]
		# print self.ops, self.ops.__class__
		o = OpsNode(self.ops.clone(), newNext)
		o.isLoop = self.isLoop 
		o.dominator = self.dominator
		o.pred = self.pred 
		return o
	def copy(self):
		if isinstance(self, TerminateNode):
			return self
		newNext = []
		for e in self.next:
			newNext += [e.copy()]
		# print self.ops, self.ops.__class__
		o = OpsNode(self.ops.clone(), newNext)
		o.isLoop = self.isLoop 
		o.dominator = self.dominator
		o.pred = self.pred 
		return o
	def appendNext(self, other):
		if not(self is other) and not isinstance(self, TerminateNode):
			if self.next == []:
				self.next = [other]
				other.pred = other.pred.union(set([self]))
			else :
				for i in range(0, len(self.next)):
					self.next[i].appendNext(other)



	def __lshift__(self, other):
		if isinstance(self, TerminateNode):
			return 
		if isinstance(self.ops, SeqOps) and self.ops.elements == [] and self.next == []:
			self.ops = other.ops
			self.next = other.next
			self.dominator = other.dominator
			self.pred = other.pred

			for i in self.next:
				i.pred -= set([other])
				i.pred = i.pred.union(set([self]))

		elif self.next == []:
			self.next = [other]
			other.pred = other.pred.union(set([self]))
		else:
			self.appendNext(other)
			# for i in self.next:
			# 	i << other
				# i << other.clone()
				# other.pred.union(set[])

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