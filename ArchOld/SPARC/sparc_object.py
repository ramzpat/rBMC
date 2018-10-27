
if __package__ is None:
  import sys
  from os import path
  sys.path.append( path.dirname(path.dirname( path.dirname( path.abspath(__file__) ) ) ))
  from Arch.objects import *
else:  
  from Arch.objects import *


# Encode Instruction object
def instr(name, operand, cond = (True)):
	statement = None
	rt = operand[1]
	opr = operand[0]
	if name == 'mova':
		# i = Instr('mova', rt, opr)
		# i.iSemantics = (lambda: [(rt << opr)])
		statement = [
			TempReg('val') << opr, 
			rt << TempReg('val')
		]
		# [(operand[0] << operand[1])]
	elif name == 'add' :
		# i = Instr('add', rt, opr)
		# i.iSemantics = (lambda: [rt << rt + opr])
		statement = [
			TempReg('v_rt') << rt, 
			TempReg('v_opr') << opr,
			TempReg('val') << TempReg('v_rt') + TempReg('v_opr'),
			rt << TempReg('val')
		]
		# [(operand[0] << (operand[0] + operand[1]))]
	elif name == 'cmp' :
		# i = Instr('cmp', rt, opr)
		# i.iSemantics = (lambda: [Register('z') << i_if_exp(rt == opr, 1, 0), 
		# 			Register('n') << i_if_exp(rt < opr, 1, 0)])
		statement = [
			TempReg('v_rt') << rt,
			TempReg('v_opr') << opr,
			TempReg('v_z') << ifExp( TempReg('v_rt') == TempReg('v_opr'), 1, 0 ),
			TempReg('v_n') << ifExp( TempReg('v_rt') != TempReg('v_opr'), 0, 1 ),
			Register('z') << TempReg('v_z'),
			Register('n') << TempReg('v_n')
		]
		# [Register('z') << i_if_exp(rt == opr, 1, 0), 
		# 			Register('n') << i_if_exp(rt < opr, 1, 0)]
	return [InstrOps(*statement)]

def instr_memory(name, addr, reg, cond = (True)):
	# cond = decode(cond)
	statement = []
	if name == 'ldub' :
		# i = Instr('ldub', reg, addr)
		# i.iSemantics = (lambda: [(reg << i_read(addr))])
		statement = [
			TempReg('val') << Location(addr),
			reg << TempReg('val')
		]
		# [(reg << i_read(addr))]
	elif name == 'ldstub' :
		# i = Instr('ldstub', reg, addr)
		# i.iSemantics = (lambda: [(reg << i_rmw(1, addr))])
		statement = [
			Atomic(TempReg('val') << Location(addr)), 
			reg << TempReg('val'),
			Atomic(Location(addr) << 1)
		] 
		# [(reg << i_rmw(1, addr))]
	# elif name == 'str':
	# 	statement = [i_write(reg, operand)]
	return [InstrOps(*statement)]

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
		b = branchOp(~(reg == 0), label)
		# SparcBranch(label, ~(reg == 0))
		b.annulled = a
		b.predict = p
		statement = [b]
	elif name == 'ba':
		b = branchOp(True, label)
		# SparcBranch(label, True)
		b.annulled = a
		b.predict = p
		statement = [b]
	return [InstrOps(*statement)]

# def instr_delaySlot(s):
# 	for i in range(0, len(s)-1):
# 		if isinstance(s[i], SparcBranch):
# 			s[i].setNext(s[i+1])
# 			s[i+1] = None
# 	return s

def delayedInstrBehavior(s):
	i = 0
	while (i < len(s)-1):
		if isinstance(s[i], InstrOps) and s[i].getBranch() != None:
			b = s[i].getBranch()
			if(b.annulled == 1):
				s[i] = InstrOps(s[i+1].elements, b )
				s[i+1] = InstrOps()
			else:
				tmp = s[i]
				s[i] = s[i+1]
				s[i+1] = tmp
				i = i + 1
		i = i + 1
	return s
