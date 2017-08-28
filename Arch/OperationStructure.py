from Operation import *
from Annotation import *

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
			print self,'...', other
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