if __package__ is None:
  import sys
  from os import path
  sys.path.append( path.dirname(path.dirname( path.dirname( path.abspath(__file__) ) ) ))
  from Arch.arch_object import *
else:  
  from Arch.arch_object import *

class SparcBranch(InstrBranch):
	def setAnnulled(self, a):
		self.annul = a 
	def setPredict(self, p):
		self.predict = p
	def __str__(self):
		return 'branch('+str(self.cond)+', '+ str(self.link)+ ', a:' + str(self.annul) + ', p:' + str(self.predict) + ')'

	def setNext(self, delaySlot):
		self.delayInstr = delaySlot

	# def unroll(self):
	# 	return ([InstrAssume(self.cond), self.delayInstr],
	# 			[InstrAssume(Exp(EOpr['not'],(self.cond))), self.delayInstr])



# fence - MEMBAR(WR)
class MEMWR(i_fence):
	def __init__(self):
		self.name = 'MEMBAR(WR)'
	def __str__(self):
		return 'MEMBAR(WR)'
		

# Encode Instruction object
def instr(name, operand, cond = (True)):
	statement = None
	rt = operand[1]
	opr = operand[0]
	if name == 'mova':
		i = Instr('mova', rt, opr)
		i.iSemantics = (lambda: [(rt << opr)])
		statement = i
		# [(operand[0] << operand[1])]
	elif name == 'add' :
		i = Instr('add', rt, opr)
		i.iSemantics = (lambda: [rt << rt + opr])
		statement = i
		# [(operand[0] << (operand[0] + operand[1]))]
	elif name == 'cmp' :
		i = Instr('cmp', rt, opr)
		i.iSemantics = (lambda: [Register('z') << i_if_exp(rt == opr, 1, 0), 
					Register('n') << i_if_exp(rt < opr, 1, 0)])
		statement = i
		# [Register('z') << i_if_exp(rt == opr, 1, 0), 
		# 			Register('n') << i_if_exp(rt < opr, 1, 0)]
	return [statement]

def instr_memory(name, addr, reg, cond = (True)):
	# cond = decode(cond)
	statement = []
	if name == 'ldub' :
		i = Instr('ldub', reg, addr)
		i.iSemantics = (lambda: [(reg << i_read(addr))])
		statement = i
		# [(reg << i_read(addr))]
	elif name == 'ldstub' :
		i = Instr('ldstub', reg, addr)
		i.iSemantics = (lambda: [(reg << i_rmw(1, addr))])
		statement = i 
		# [(reg << i_rmw(1, addr))]
	# elif name == 'str':
	# 	statement = [i_write(reg, operand)]
	return [statement]

def instr_branch(br, reg, label):
	statement = []
	name = br[0]
	p = 1 # default pt (predict)
	a = 0 # annulled bit

	if len(br) > 2:
		p = 0 if br[2] == 'pn' else 1
		a = 1 if br[1] == 'a' else 0
	elif len(br) == 2:
		if br[1] == 'a':
			a = 1
		elif br[1] == 'pt':
			p = 1
		elif br[1] == 'pn':
			p = 0

	if name == 'brnz':
		b = SparcBranch(label, ~(reg == 0))
		b.setAnnulled(a)
		b.setPredict(p)
		b.iSemantics = (lambda self: [self])
		statement = [b]
	elif name == 'ba':
		b = SparcBranch(label, True)
		b.setAnnulled(a)
		b.setPredict(p)
		b.iSemantics = (lambda self: [self])
		statement = [b]
	return statement

# ---------- Intermediate semantics
def instr_sem(name, operand, cond = (True)):
	# cond = decode(cond)
	statement = []
	rt = operand[0]
	opr = operand[1]
	if name == 'mov' or name == 'MOV' :
		statement = [(operand[0] << operand[1])]
	elif name == 'add' :
		statement = [(operand[0] << (operand[0] + operand[1]))]
	elif name == 'cmp' :
		statement = [Register('z') << i_if_exp(rt == opr, 1, 0), 
					Register('n') << i_if_exp(rt < opr, 1, 0)]
	return statement

def instr_memory_sem(name, addr, reg, cond = (True)):
	# cond = decode(cond)
	statement = []
	if name == 'ldub' :
		statement = [(reg << i_read(addr))]
	elif name == 'ldstub' :
		statement = [(reg << i_rmw(1, addr))]
	# elif name == 'str':
	# 	statement = [i_write(reg, operand)]
	return statement

def instr_branch(br, reg, label):
	statement = []
	name = br[0]
	p = 1 # default pt (predict)
	a = 0 # annulled bit

	if len(br) > 2:
		p = 0 if br[2] == 'pn' else 1
		a = 1 if br[1] == 'a' else 0
	elif len(br) == 2:
		if br[1] == 'a':
			a = 1
		elif br[1] == 'pt':
			p = 1
		elif br[1] == 'pn':
			p = 0
	if name == 'brnz':
		b = SparcBranch(label, ~(reg == 0))
		b.setAnnulled(a)
		b.setPredict(p)
		statement = [b]
	elif name == 'ba':
		b = SparcBranch(label, True)
		b.setAnnulled(a)
		b.setPredict(p)
		statement = [b]
	return statement

def instr_fence():
	statement = [MEMWR()]
	return statement


# def instr_delaySlot(s):
# 	for i in range(0, len(s)-1):
# 		if isinstance(s[i], SparcBranch):
# 			s[i].setNext(s[i+1])
# 			s[i+1] = None
# 	return s
