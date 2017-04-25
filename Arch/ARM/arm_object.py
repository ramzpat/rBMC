
if __package__ is None:
  import sys
  from os import path
  sys.path.append( path.dirname(path.dirname( path.dirname( path.abspath(__file__) ) ) ))
  from Arch.arch_object import *
else:  
  from Arch.arch_object import *

from lexer import lexer as arm_lexer, tokens as arm_tokens, literals as arm_literals

ARMInstrList = ['ldr', 'str', 'mov', 'dsb', 'dmb', 'cmp', 'add', 'sub', 'b']
ARMCondList = ['eq', 'ne', 'cs', 'cc', 'mi', 'pl', 'vs', 'vc', 'al']
ARMRegList = ['r1','r2','r3','r4','r5','r6','r7','r8','r9', 'z', 'n', 'c', 'v']
ARMLocList = ['res', 'res_addr']


# dynamic instruction
class ARMInstr(Instr):
	# paramSet = 0
	def is_( instr, other):
		print 'is check'
		return instr.instr_name == other
	def is_not(insr, other):
		print 'is check'
		return instr.instr_name == other

	def InstrName(self, i):
		return ARMInstrList[i]

	def __str__(self):
		cond = ''
		if self.operands:
			cond = self.operands[0]
		op = ''
		if len(self.operands[1:]):
			op = str(self.operands[1])
			for o in self.operands[2:]:
				op += ', ' + str(o)
		return self.InstrName(self.instr_name)+str(cond)+ " " + str(op)

# static instruction
class ARMDMB(ARMInstr):
	def __init__(self):
		ARMInstr.__init__(self, 'dmb')

	def InstrName(self, i):
		return 'dmb'
class ARMDSB(ARMInstr):
	def __init__(self):
		ARMInstr.__init__(self, 'dsb')
	def InstrName(self, i):
		return 'dsb'

# init class 
k = 0
for i in ARMInstrList:
	ARMInstr.__dict__[i] = k
	k+=1
ARMInstr.__dict__['dsb'] = ARMDSB()
ARMInstr.__dict__['dmb'] = ARMDMB()
# ARMInstr.__dict__ = dict(zip(ARMInstrList, range(len(ARMInstrList))))

class ARMReg(Register):
	def RegName(self, i):
		return self.reg_name
# init reg
for i in ARMRegList:
	ARMReg.__dict__[i] = ARMReg(i)

class ARMCond:
	def __init__(self, code, id = 0):
		self.code = code 
	def __str__(self):
		if self.code == 'al':
			return ''
		return str(self.code)
k = 0
for i in ARMCondList:
	ARMCond.__dict__[i] = ARMCond(i, k)
	k+=1
# ARMCond = enum(*ARMCondList)


class ARMLoc(Location):
	

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
	# return statement
	return [Instr(name, [cond] + operand)]

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
	# return statement
	return [Instr(name, [cond, reg, operand])]
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



class ARMObject:
	def __init__(self, iName, *param):
		pass 

class Semantics:
	# iico
	# partial order 
	def parseInstr(ii):
		pass 

class ARMSem(Semantics):
	def parseInstr(ii):
		pass 


if __name__ == '__main__':
	ARMObject('test', 'a', 'b', 'c')