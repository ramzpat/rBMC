# Semantics of operations 

from z3 import *
import itertools

from annotation import *


# ----------------- Operations
class Operation(AnnotatedStatement):
	def __init__(self):
		pass 

# <var> := <exp>
# <var> ::= <reg> | <loc> | <symbolic var>
class Assignment(Operation):
	def __init__(self, var, exp):
		self.var = var
		self.exp = exp

	def __str__(self):
		return str(self.var) + " := " + str(self.exp) + ' (' + str(self.__class__) + ')' 

# <loc> := <val> {symbolic / concrete}
class WriteAssn(Assignment):
	pass 

# <reg> := <val> {symbolic / concrete}
class ReadAssn(Assignment):
	pass 

# fence()
class fenceStm(Operation):
	def __init__(self):
		pass
	def __str__(self):
		return 'fence()' 
class branchOp(Operation):
	def __init__(self):
		pass 
	def __str__(self):
		return 'branch()'

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

# atomic{ ... }
class AtmStm(SeqSem):
	pass

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



if __name__ == '__main__':
	print 'hello operation semantics'

	P = InstrSem(
			ReadAssn('r', '1'), 
			ParallelSem(
				ReadAssn('r', '2'),
				ReadAssn('r', '3')), 
			Assertion('test')
			)
	A = CodeStructure(SeqSem(ReadAssn('r', '4')))
	B = CodeStructure(SeqSem(ReadAssn('r', '6'), havoc('r1', 'r2')))
	t = CodeStructure(P, [A, B])
	print t[1]
	for p in CodeStructure(P, [A, B]):
		print p
		print '-----'

	# for e in P:
	# 	print str(e)
