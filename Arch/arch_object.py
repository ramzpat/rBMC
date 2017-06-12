# architecture object
# arch_object.py

if __package__ is None:	
	import sys
	from os import path
	sys.path.append((path.dirname( path.dirname( path.abspath(__file__) ) ) ))
	from HWModel.OperatorSem import *
else:
	from HWModel.OperatorSem import *

from abc import ABCMeta, abstractmethod

# ======== ASM Objects 

# enumurator for Instr name
# http://stackoverflow.com/questions/36932/how-can-i-represent-an-enum-in-python
# Numbers = enum('ZERO', 'ONE', 'TWO')
def enum(*sequential, **named):
    enums = dict(zip(sequential, range(len(sequential))), **named)
    return type('Enum', (), enums)
    # return enums



# Expressions
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

# ======== <arch> ASM Objects 
# -- Instruction 
class Instr:
	
	is_branch = False 

	def unroll(self):
		return ([InstrAssume(self.operands[0])], [InstrAssume(Exp(EOpr['not'],(self.operands[0])))])

	def InstrName(self, i):
		return 'undefined_instr'
	writeSet = set([])
	readSet = set([])
	operands = [] 
	
	def __init__(self, name, *operands):
		self.instr_name = name
		self.parent = self
		if len(operands):
			if type(operands[0]) == list:
				operands = operands[0]
			self.operands = [o for o in operands]

		# For data dependece
		self.writeSet = set([])
		self.readSet = set([])

		# self.operands = operands
		# self.cond = cond 
	def is_(self, instr, other):
		print 'is check'
		return False
	# For an instruction that generate multiple instances
	def parent(self, parent):
		self.parent = parent

	def __str__(self):
		op = ''
		if len(self.operands):
			op += str(self.operands[0])
			# return str(self.operands)
			for opr in self.operands[1:]:
				op += ',' + str(opr)
		return self.InstrName(self.instr_name)+' '+op
		# return str(self.instr_name)

	def iSemantics(self):
		return [self]

	def behavior(self):
		return None


# --- Label
class Label:
	def __init__(self, label_name):
		self.label_name = label_name
	def lname(self):
		return self.label_name
	def __str__(self):
		# return 'label(' + self.label_name + ')'
		return str(self.label_name) + ":"
	def __eq__(self, other):
		if isinstance(other, str):
			return self.label_name == other
		else :
			return self.label_name == other.label_name

# --- Branch
class InstrBranch(Instr):
	def __init__(self, label_name, cond):
		self.instr_name = 'branch'
		self.link = label_name
		self.cond = cond 

	def condition(self):
		return self.cond
	def targetLabel(self):
		return self.link

	def unroll(self):
		return ([InstrAssume(self.cond)], [InstrAssume(Exp(EOpr['not'],(self.cond)))])

	def __str__(self):
		return 'branch(' + str(self.cond) + "," + self.link + ')'

# -- Assert (cond)
class InstrAssert(Instr):
	def __init__(self, cond):
		self.instr_name = 'assert'
		self.cond = cond 
	def __str__(self):
		return 'assert(' + str(self.cond) + ')'	

# -- Assume (cond)
class InstrAssume(Instr):
	def __init__(self, cond):
		self.instr_name = 'assume'
		self.cond = cond 
	def __str__(self):
		return 'assume(' + str(self.cond) + ')'

# -- Intermediate Language
class iSemantics(Instr):
	def setParent(self, node):
		self.parent = node

# -- rmw(rt, addr)
class i_rmw(iSemantics):
	def __init__(self, rt, addr):
		# self.rmw = rmw 
		self.rt = rt
		self.addr = addr 
	def __str__(self):
		return 'rmw(' + str(self.rt) + ',' +  str(self.addr) + ')'

# -- read(addr)   // exp
class i_read(iSemantics):
	def __init__(self, opr):
		# self.read = read 
		self.opr = opr 
	def __str__(self):
		return 'load('+ str(self.opr) + ')'

# -- write(rt, addr)
class i_write(iSemantics):
	def __init__(self, rt, addr):
		# self.write = write 
		self.rt = rt
		self.addr = addr
	def __str__(self):
		return 'store(' + str(self.rt) + ','  + str(self.addr) + ')'

# -- var := exp
class i_assignment(iSemantics):
	def __init__(self, var, expression):
		self.var = var
		self.expression = expression
	def __str__(self):
		return str(self.var) + ' := ' + str(self.expression)

# -- if ( cond ) Statements 
class i_if(iSemantics):
	def __init__(self, cond, statement):
		self.cond = cond
		self.statement = statement
	def __str__(self):
		statement = [ str(s) + "; " for s in self.statement] 
		return "if(" + str(self.cond) + ")" + str(statement)

# -- ( cond )? True_exp : False_exp;
class i_if_exp(iSemantics):
	def __init__(self, cond, t_exp, f_exp):
		self.cond = cond
		self.t_exp = t_exp
		self.f_exp = f_exp
	def __str__(self):
		return "(" + str(self.cond) + ")? " + str(self.t_exp) + ":" + str(self.f_exp)

# -- ( cond )? True_exp : False_exp;
# Arithmetic calculation
class ifExp(Exp):
	def __init__(self, cond, t_exp, f_exp):
		self.cond = cond
		self.t_exp = t_exp
		self.f_exp = f_exp
	def __str__(self):
		return "(" + str(self.cond) + ")? " + str(self.t_exp) + ":" + str(self.f_exp)

class i_special (iSemantics):
	pass

# class Var(Exp):
	# pass

# -- Register
class Register(Exp):

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

class TempReg(Register):
	def RegName(self, i):
		return self.reg_name

	def __lshift__(self, other):
		if isinstance(other, Location):
			return ReadAssn(self, other)
		elif isinstance(other, Register):
			return ReadAssn(self, other)
		else:
			# return WriteAssn(self, other)
			return Assignment(self, other)

class Location(Exp):
	def __init__(self, address = 0):
		# self.name = name
		self.address = address # exp

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

# def is_reg(reg):
# 	return isinstance(reg, Register)

if __name__ == "__main__":
	i = Instr('ldr', 'r1', '[r2]')
	# print 
