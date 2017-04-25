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
		return str(self.var) + " := " + str(self.exp)

# <loc> := <val> {symbolic / concrete}
class WriteAssn(Assignment):
	pass 

# <reg> := <val> {symbolic / concrete}
class ReadAssn(Assignment):
	pass 

class Assertion(iSem):
	pass

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
		self.statement = statement
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


if __name__ == "__main__":
	# symbolic executed programs = partial order = list of list of ....
	symP = [
		ReadAssn('r', '1'),
		ReadAssn('r', '2'),
	]

	for e in symP:
		print str(e)
