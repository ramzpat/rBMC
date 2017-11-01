
from Operation import *

EOpr = {
	'plus' : '+',
	'minus' : '-',
	'times' : '*',
	'divide' : '/',

	'eq' : '==',
	'lt' : '<',
	'gt' : '>',
	'not' : '!',
	'and' : 'and', 
	'or' : 'or',
}

class Exp: # Value expression
	def __init__(self, *v):
		self.val = v

	def __hash__(self):
		return hash(self.val)

	def val(self):
		return self.val

	def __len__(self):
		# print self.val
		return len(self.val)

	def __getitem__(self,index):
		return self.val[index]
	
	def __str__(self):
		s = str(self.val[0])
		if len(self.val) == 1:
			return s
		for v in self.val[1:]:
			s = s + " " + str(v)
		return '(' + s + ')' 

	def __add__(self, other):
		return Exp(self, EOpr['plus'], other)
	def __radd__(self, other):
		return Exp(other, EOpr['plus'], self)
	def __sub__(self, other):
		return Exp(self, EOpr['minus'], other)
	def __rsub__(self, other):
		return Exp(other, EOpr['minus'], self)
	def __mul__(self, other):
		return Exp(self, EOpr['times'], other)
	def __rmul__(self, other):
		return Exp(other, Eopr['times'], self)
	def __div__(self, other):
		return Exp(self, EOpr['divide'], other)
	def __rdiv__(self, other):
		return Exp(other, EOpr['divide'], self)
	def __eq__(self, other):
		return Exp(self, EOpr['eq'], other)
	def __lt__(self, other):
		return Exp(self, EOpr['lt'], other)
	def __gt__(self, other):
		return Exp(self, EOpr['gt'], other)
	def __ne__(self, other):
		return Exp(EOpr['not'], Exp(self, EOpr['eq'], other))
	def __and__(self, other):
		return Exp(self, EOpr['and'], other)
	def __rand__(self, other):
		return Exp(other, EOpr['and'], self)
	def __or__(self, other):
		return Exp(self, EOpr['or'], other)
	def __ror__(self, other):
		return Exp(other, EOpr['or'], self)
	def __not__(self):
		return Exp(EOpr['not'], self)
	def not_(self):
		return Exp(EOpr['not'], self)
	def __invert__(self):
		return Exp(EOpr['not'], self)
	def __le__(self, other):
		# print (self == other) & (self < other)
		return (self == other) | (self < other)
	def __ge__(self, other):
		return (self == other) | (self > other)

	def __lshift__(self, other):
		return Assignment(self, other)

class undefinedExp(Exp):
	def __str__(self):
		return '*'

def bool_and(e1, e2):
	return Exp(e1, EOpr['and'], e2)
def bool_or(e1, e2):
	return Exp(e1, EOpr['or'], e2)
def bool_not(exp):
	return not exp

# -- ( cond )? True_exp : False_exp;
# Arithmetic calculation
class ifExp(Exp):
	def __init__(self, cond, t_exp, f_exp):
		self.cond = cond
		self.t_exp = t_exp
		self.f_exp = f_exp
	def __str__(self):
		return "(" + str(self.cond) + ")? " + str(self.t_exp) + ":" + str(self.f_exp)
	def __len__(self):
		return 0

# -- Register
class Register(Exp):

	def clone(self):
		return self.__class__(self.reg_name)
	def RegName(self, i):
		return self.reg_name
		# return 'undefined_reg'

	def __init__(self, name):
		self.reg_name = name

	def __str__(self):
		return self.RegName(self.reg_name)

	def __lshift__(self, other):
		if isinstance(other, Location):
			return ReadAssn(self, other)
		else:
			return WriteAssn(self, other)
			# return Assignment(self, other)

	def __hash__(self):
		return hash(self.reg_name)

	def __len__(self):
		return 0

class TempReg(Register):

	def clone(self):
		return self.__class__(self.reg_name)
	def RegName(self, i):
		return self.reg_name

	def __lshift__(self, other):
		if isinstance(other, Location):
			return ReadAssn(self, other)
		elif isinstance(other, Register) and not isinstance(other, TempReg):
			return ReadAssn(self, other)
		elif isinstance(other, AuxVar):
			return ReadAssn(self, other)
		# elif isinstance(other, Resv):
		# 	return ReadAssn(self, other)
			# assert(False)
		else:
			# return WriteAssn(self, other)
			return Assignment(self, other)

class Location(Exp):
	def __init__(self, address = 0):
		# self.name = name
		self.address = address # exp

	def clone(self):
		return self.__class__(self.address)

	def __str__(self):
		return "[" + str(self.address) + "]"
	def __lshift__(self, other_address):
		return WriteAssn(self, other_address)
	def __hash__(self):
		return hash(self.address)
	def __len__(self):
		return 0
	# def __eq__(self, other):
	# 	return self.address == other.address

class AuxVar(Exp):
	def __init__(self, var):
		self.name = var 
	def clone(self):
		return self.__class__(self.name)
	def __str__(self):
		return '$' + str(self.name)
	def __lshift__(self, other):
		if isinstance(other, TempReg):
			return WriteAssn(self, other)
		else:
			return WriteAssn(self, other)
		assert(False)
	def __len__(self):
		return 0





