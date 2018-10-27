
if __package__ is None:
  import sys
  from os import path
  sys.path.append( path.dirname(path.dirname( path.dirname( path.abspath(__file__) ) ) ))
  # from Ops.objects import *
# else:  
from Ops.objects import *

from lexer import lexer as arm_lexer, tokens as arm_tokens, literals as arm_literals

def decode(e):
	if(e == 'eq'):
		cond = (Register('z') == int(1))
	elif(e == 'ne'):
		cond = (Register('z') == int(0))
	elif(e == 'cs' or e == 'hs'):
		cond = (Register('c') == int(1))
	elif(e == 'cc' or e == 'lo'):
		cond = (Register('c') == int(0))
	elif(e == 'mi'): # negative
		cond = (Register('n') == int(1))
	elif(e == 'pl'): # positive
		cond = (Register('n') == int(0))
	elif(e == 'vs'): 
		cond = (Register('v') == int(1))
	elif(e == 'vc'): 
		cond = (Register('v') == int(0))
	else:
		cond = e
	return cond


def instr(name, operand, cond = (True)):
	# cond = decode(cond)
	statement = []
	rt = operand[0]
	opr = operand[1]
	if name == 'mov' or name == 'MOV' :
		statement = [
			TempReg('val') << operand[1],
			operand[0] << TempReg('val')
		]
	elif name == 'add' :
		ii = (operand[0] << (operand[0] + operand[1]))
		statement = [
			ParOps(
				TempReg('v1') << operand[0],
				TempReg('v2') << operand[1]
			),
			operand[0] << (TempReg('v1') + TempReg('v2'))
		]
	elif name == 'cmp' :
		z = Register('z')
		n = Register('n')
		ii_1 = SeqOps(
			TempReg('val_z') << ifExp(rt == opr, 1, 0),
			z << TempReg('val_z')
			)
		ii_2 = SeqOps(
			TempReg('val_n') << ifExp(rt < opr, 1, 0),
			n << TempReg('val_n')
			)
		statement = [ParOps(TempReg('rt') << rt, TempReg('rd') << opr), ParOps(ii_1, ii_2) ]
	if cond != True:
		cond = decode(cond)
		iif = CondOps(cond, SeqOps(*statement))
		statement = [iif]
	return [InstrOps(*statement)]
	# return [Instr(name, [cond] + operand)]

def instr_memory(name, reg, operand, cond = (True)):
	# cond = decode(cond)
	statement = []
	if name == 'ldr' :
		# ii = (reg << i_read(operand))
		statement = [
			TempReg('val') << Location(operand),
			reg << TempReg('val')
		]
	elif name == 'str':
		statement = [
			TempReg('val') << reg,
			Location(operand) << TempReg('val') 
			# TempReg('val') << Location(operand),
			# reg << TempReg('val')
		]
	if cond != True:
		cond = decode(cond)
		iif = CondOps(cond, SeqOps(*statement))
		statement = [iif]
	return [InstrOps(*statement)]
	# return [Instr(name, [cond, reg, operand])]
def instr_swp(rd, reg, operand, cond = (True)):
	rd = (rd)
	rt = (reg)
	# print reg.__class__
	# ii = rd << i_rmw(reg, operand)
	# ii.readSet = set([reg])
	# ii.writeSet = set([rd])
	return [
		InstrOps(
			TempReg('val_rt') << rt,
			Atomic(TempReg('val') << Location(operand)),
			rd << TempReg('val'),
			Atomic(Location(operand) << TempReg('val_rt'))
		)
	]

def instr_branch(link, cond = (True)):
	# cond = decode(cond)
	# ii = ARMBranch(link, cond)
	# ii.decode(cond)
	return [InstrOps(branchOp(decode(cond), Label(link)))]



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