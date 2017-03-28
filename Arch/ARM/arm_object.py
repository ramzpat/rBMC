
if __package__ is None:
  import sys
  from os import path
  sys.path.append( path.dirname(path.dirname( path.dirname( path.abspath(__file__) ) ) ))
  from Arch.arch_object import *
else:  
  from Arch.arch_object import *

from lexer import lexer as arm_lexer, tokens as arm_tokens, literals as arm_literals

class ARMIf(i_if):
	def decode(self, e):
		if(e == 'eq'):
			self.cond = (Register('z') == int(1))
			self.readSet |= set([Register('z')])
		elif(e == 'ne'):
			self.cond = (Register('z') == int(0))
			self.readSet |= set([Register('z')])
		elif(e == 'cs' or e == 'hs'):
			self.cond = (Register('c') == int(1))
			self.readSet |= set([Register('c')])
		elif(e == 'cc' or e == 'lo'):
			self.cond = (Register('c') == int(0))
			self.readSet |= set([Register('c')])
		elif(e == 'mi'): # negative
			self.cond = (Register('n') == int(1))
			self.readSet |= set([Register('n')])
		elif(e == 'pl'): # positive
			self.cond = (Register('n') == int(0))
			self.readSet |= set([Register('n')])
		elif(e == 'vs'): 
			self.cond = (Register('v') == int(1))
			self.readSet |= set([Register('v')])
		elif(e == 'vc'): 
			self.cond = (Register('v') == int(0))
			self.readSet |= set([Register('v')])
		else:
			self.cond = e

class ARMBranch(InstrBranch):
	def decode(self, e):
		if(e == 'eq'):
			self.cond = (Register('z') == int(1))
			self.readSet |= set([Register('z')])
		elif(e == 'ne'):
			self.cond = (Register('z') == int(0))
			self.readSet |= set([Register('z')])
		elif(e == 'cs' or e == 'hs'):
			self.cond = (Register('c') == int(1))
			self.readSet |= set([Register('c')])
		elif(e == 'cc' or e == 'lo'):
			self.cond = (Register('c') == int(0))
			self.readSet |= set([Register('c')])
		elif(e == 'mi'): # negative
			self.cond = (Register('n') == int(1))
			self.readSet |= set([Register('n')])
		elif(e == 'pl'): # positive
			self.cond = (Register('n') == int(0))
			self.readSet |= set([Register('n')])
		elif(e == 'vs'): 
			self.cond = (Register('v') == int(1))
			self.readSet |= set([Register('v')])
		elif(e == 'vc'): 
			self.cond = (Register('v') == int(0))
			self.readSet |= set([Register('v')])
		else:
			self.cond = e

def instr(name, operand, cond = (True)):
	# cond = decode(cond)
	statement = []
	rt = operand[0]
	opr = operand[1]
	if name == 'mov' or name == 'MOV' :
		ii = (operand[0] << operand[1])
		if isinstance(operand[1], Register):
			ii.readSet = set([operand[1]])
		ii.writeSet = set([operand[0]])
		statement = [ii]
	elif name == 'add' :
		ii = (operand[0] << (operand[0] + operand[1]))
		if isinstance(operand[1], Register):
			ii.readSet = set([operand[1]])
		ii.readSet |= set([operand[0]])
		ii.writeSet = set([operand[0]])
		statement = [ii]
	elif name == 'cmp' :
		z = Register('z')
		n = Register('n')
		ii_1 = z << i_if_exp(rt == opr, 1, 0)
		ii_2 = n << i_if_exp(rt < opr, 1, 0)

		ii_1.readSet = set([rt])
		ii_1.writeSet = set([z])
		ii_2.readSet = set([rt])
		ii_2.writeSet = set([n])
		statement = [ii_1, ii_2]
	if cond != True:
		iif = ARMIf(cond, statement)
		iif.decode(cond)
		statement = [iif]
	return statement

def instr_memory(name, reg, operand, cond = (True)):
	# cond = decode(cond)
	statement = []
	if name == 'ldr' :
		ii = (reg << i_read(operand))
		ii.writeSet = set([reg])
		statement = [ii]
	elif name == 'str':
		ii = i_write(reg, operand)
		ii.readSet = set([reg])
		statement = [ii]
	return statement
def instr_swp(rd, reg, operand, cond = (True)):
	# rd = Register(rd)
	# rt = Register(reg)
	# print type(reg)
	ii = rd << i_rmw(reg, operand)
	ii.readSet = set([reg])
	ii.writeSet = set([rd])
	return [ii]

def instr_branch(link, cond = (True)):
	# cond = decode(cond)
	ii = ARMBranch(link, cond)
	ii.decode(cond)
	return [ii]