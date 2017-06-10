from z3 import *
import itertools

# intermediate semantics
#  P = <N, E, n0, f>
#  directed graph


def printSemantics(sem, indent = 0):
	if type(sem) == tuple and len(sem):
		print str(' ' * indent) + '('
		printSemantics(sem[0], indent + 1)
		for s in sem[1:]:
			print str(' ' * (indent+1)) + '||'
			printSemantics(s, indent + 1)
		print str(' ' * indent) + ')'
	elif type(sem) == list and len(sem):
		print str(' ' * indent) + '['
		printSemantics(sem[0], indent + 1)
		for s in sem[1:]:
			# print ' >> '
			printSemantics(s, indent + 1)
		print str(' ' * indent) + ']'
	elif sem:
		if isinstance(sem, ifSem):
			print str(' ' * indent) + str(sem.cond) + ' -> '
			printSemantics(sem.statement, indent + 2)
			# print str(' ' * indent) + '!' + str(sem.cond)
		else:
			print str(' ' * (indent)) + str(sem)


# Operator : assignment, assertion, fence, atomic 
class iSem:
	def __init__(self, name = ''):
		self.name = name

	def __str__(self):
		return "Not implemented yet"

# <var> := <exp>
# <var> ::= <reg> | <loc> | <symbolic var>
class Assignment(iSem):
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

class Assertion(iSem):
	pass

# fence 
class ffence(iSem):
	def __init__(self, name = 'ffence'):
		iSem.__init__(self, name) 

	def __str__(self):
		return "ffence:"+self.name

class lwfence(iSem):
	def __init__(self, name = 'lwfence'):
		iSem.__init__(self, name) 

	def __str__(self):
		return "lwfence:"+self.name
class ifSem(iSem):
	def __init__(self, cond, statement):
		iSem.__init__(self, 'condition')
		self.cond = cond
		self.statement = (statement)
	def __str__(self):
		return '(' + str(self.cond) + ') -> ' + str(self.statement)


# for supporting programming logic 
class labelSem(iSem):
	def __str__(self):
		return str(self.name) + ':'
class gotoSem(iSem):
	def __init__(self, label):
		self.name = 'goto'
		self.label = label

	def __str__(self):
		return 'goto ' + str(self.label)


class SeqSem:
	def __init__(self, *seq):
		# print type(seq)
		self.seq = (seq)
		for i in self.seq:
			# print i.__class__
			assert( isinstance(i, iSem) or isinstance(i, SeqSem) )

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
		
		

class ParallelSem(SeqSem):
	def __init__(self, *par):
		self.par = list(par)
		for i in self.par:
			assert( isinstance(i, iSem) or isinstance(i, SeqSem) )

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

if __name__ == "__main__":
	# symbolic executed programs = partial order = list of list of ....
	symP = [
		ReadAssn('r', '1'),
		ReadAssn('r', '2'),
	]

	P = SeqSem(ReadAssn('r', '1'), ParallelSem(ReadAssn('r', '2'),ReadAssn('r', '3')))
	print P

	for e in P:
		print str(e)
