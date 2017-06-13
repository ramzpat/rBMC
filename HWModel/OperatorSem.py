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


# --------- CodeBlock 
class CodeBlock():
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
				for p in i:
					yield SeqSem(self.body, p)
	def __getitem__(self, key):
		return SeqSem(self.body, self.next[key].getSem())
	def getSem(self, key = 0):
		if self.next:
			return self.body + self.next[key].getSem()
		return self.body

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

	def __lshift__(self, other):
		assert(isinstance(other, Operation) or isinstance(other, AnnotatedStatement) or isinstance(other, SeqSem) or 
			isinstance(other, CodeStructure))
		body = self.body
		next = self.next
		if isinstance(other, CodeStructure):
			if next == []:
				self.body += other.body
				self.next = other.next
				# self.next = [other]
			else:
				# a = self.next[0]
				# print self.next[0]
				# a << other
				# print a
				self.next[0] << other
				

				# for i in self.next:
				# 	i += other
		elif next == []:

			self.body += other
		else: 
			self.next[0] += other

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
	A = CodeBlock(SeqSem(ReadAssn('r', '4')))
	B = CodeBlock(SeqSem(ReadAssn('r', '6'), havoc('r1', 'r2')))
	t = CodeBlock(P, [A, B])
	print t[1]
	for p in CodeBlock(P, [A, B]):
		print p
		print '-----'

	# for e in P:
	# 	print str(e)
