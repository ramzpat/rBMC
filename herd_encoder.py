
from Arch.arch_object import *
from HWModel.OperatorSem import *

import HWModel.herd_framework as herd
from herd_ssa import *

locationAddr = []

MemOp = []

def encodeExp(exp, pid = 0):
	if isinstance(exp, int) or isinstance(exp, bool):
		return exp
	elif isinstance(exp, Register):
		return herd.Const(str(exp), herd.Val)
	elif isinstance(exp, Exp):
		# print exp
		if(len(exp) > 2):
			op = exp[1]
			if op == EOpr['plus']:
				return encodeExp(exp[0], pid) + encodeExp(exp[2], pid)
			elif op == EOpr['minus']:
				return encodeExp(exp[0], pid) - encodeExp(exp[2], pid)
			elif op == EOpr['times']:
				return encodeExp(exp[0], pid) * encodeExp(exp[2], pid)
			elif op == EOpr['divide']:
				return encodeExp(exp[0], pid) / encodeExp(exp[2], pid)
			elif op == EOpr['eq']:
				return (encodeExp(exp[0], pid) == encodeExp(exp[2], pid))
			elif op == EOpr['lt']:
				return encodeExp(exp[0], pid) < encodeExp(exp[2], pid)
			elif op == EOpr['gt']:
				return encodeExp(exp[0], pid) > encodeExp(exp[2], pid)
			elif op == EOpr['and']:
				return And(encodeExp(exp[0], pid),encodeExp(exp[2], pid))
			elif op == EOpr['or']:
				return Or(encodeExp(exp[0], pid),encodeExp(exp[2], pid))
		elif len(exp) == 2:
			if exp[0] == EOpr['not']:
				return Not(encodeExp(exp[1], pid))
		else:
			return encodeExp(exp[0], pid)


def encodeISem(i, pid = 0):
	# assert(isinstance(i,iSem))
	if isinstance(i, WriteAssn):
		if (isinstance(i.var, Location)):
			addr = i.var.address
			exp = i.exp
			w = herd.new_write(str(i), (addr), str(exp), pid)
			# print str(i) + ' -> \t ' + str(w)
			# MemOp += [w]
			return w
		else:
			return None
	elif isinstance(i, ReadAssn):
		if (isinstance(i.exp, Location)):
			addr = i.exp.address
			var = i.var
			
			r = herd.new_read(str(i), (addr), str(var), pid)
			# print str(i) + ' -> \t ' + str(r)
			# MemOp += [r]
			return r
		else :
			return None
	elif isinstance(i, Assignment):
		# pass
		# print i
		assn = ( herd.Const(str(i.var), herd.Val) == encodeExp(i.exp) )
		print str(i) + ' -> \t ' + str(assn)
		# (herd.Int('a') == 1)
		return assn
		# assert(False)
		# return None
	else:
		assert(False)

def encodeSem(i, pid = 0):
	if isinstance(p, ParallelSem):
		newPar = []
		for i in p.list():
			newPar += self.additionalRead(i)

		return [ParallelSem(*newPar)]
	elif isinstance(p, SeqSem):
		newSeq = []
		for i in p.list():
			newSeq += self.additionalRead(i)
		# print SeqSem(*newSeq)
		return [SeqSem(*newSeq)]
	else:
		return [p]

# def encodeMemOp(p):
# 	assert(isinstance(p, SeqSem) or isinstance(p, iSem))
# 	if isinstance(p, iSem):
# 		return encodeISem(p)
# 	elif isinstance(p, ParallelSem):


# result a set of formulas ?
def encode(p):

	def constructPO(p, prev = []):
		if isinstance(p, iSem):
			ret = []
			for i in prev:
				ret += [(i, p)]
			return (ret, [p])
		elif isinstance(p, ParallelSem):
			poRet = []
			lastEle = []
			for pl in p.list():
				(po,e) = constructPO(pl, prev)
				lastEle += e 
				poRet += po
			return (poRet, lastEle)
		elif isinstance(p, SeqSem):
			poRet = []
			for pl in p.list():
				(po,e) = constructPO(pl, prev)
				poRet += po
				prev = e 
			return (poRet, prev)
			

	def constructIICO(p):
		ret = []
		if isinstance(p, InstrSem):
			(iico, e) = constructPO(p)
			ret += iico 
		elif isinstance(p, SeqSem):
			for i in p.list():
				ret += constructIICO(i)
		return ret

	# derive the set of events
	# events = [e for e in p]
	Ev = []
	print '----'
	# info = encodeSem(p)
		# print e
		# Ev += [e]
	# for i in a + herd.global_axioms:
	# 	print i
	# derive po
	# (poS,e) = constructPO(p)
	# derive iico
	# iico = constructIICO(p)
	# RW_S = []
	# print poS
	#PoS = [e for (e, loc, )]

	# execution
	# (po, axiom_po) = herd.program_order(poS, Ev)
	# (co, axiom_co) = conflict_order(Ev)
	# (rf, axiom_rf) = read_from(Ev)

def test():

	ssaP1 = SeqSem(
		# mov r1, 0
		InstrSem(
			TempReg('result_0') << int(0),
			Register('r1_0') << TempReg('result_0')
		),
		# mov r5, 1
		InstrSem(
			TempReg('result_5') << int(1),
			Register('r5') << TempReg('result_5')
		),
		# mov r2, 1
		InstrSem(
			TempReg('result_1') << int(1),
			Register('r2_0') << TempReg('result_1')
		),
		# str r2, [r1]
		InstrSem(
			ParallelSem(
				TempReg('addr_0') << Register('r1_0'),
				TempReg('val_0') << Register('r2_0')
			),
			Location(TempReg('addr_0')) << TempReg('val_0')
		),
		# str r2, [r1+1]
		InstrSem(
			ParallelSem(
				TempReg('addr_1') << Register('r5'),
				TempReg('val_1') << Register('r2_0')
			),
			Location(TempReg('addr_1')) << TempReg('val_1')
		)
	)

	ssaP2 = SeqSem(
		# mov r1, 0
		InstrSem(
			TempReg('result_1') << int(0),
			Register('r1_1') << TempReg('result_1')
		),
		# mov r5, 1
		InstrSem(
			TempReg('result_5') << int(1),
			Register('r5') << TempReg('result_5')
		),
		# ldr r3, [r1+1]
		InstrSem(
			TempReg('addr_2') << Register('r5'),
			TempReg('result_2') << Location(TempReg('addr_2')),
			Register('r3_0') << TempReg('result_2')
		),
		# ldr r4, [r1]
		InstrSem(
			TempReg('addr_3') << Register('r1_1'),
			TempReg('result_3') << Location(TempReg('addr_3')),
			Register('r4_0') << TempReg('result_3')
		)
	)
	ssaP = SeqSem(
		Location(0) << int(0),
		Location(1) << int(0),
		ParallelSem(ssaP1, ssaP2)
		)
	# print ssaP
	f = encode(ssaP)

def mp():
	P1 = SeqSem(
		InstrSem(	# mov r1, #1
			TempReg('val') << 1, 
			Register('r1') << TempReg('val')
			),
		InstrSem(	# str r1, [x]
			TempReg('val') << Register('r1'),
			ParallelSem(TempReg('val1') << Register('val'), TempReg('val2') << Register('val')),
			Location('x') << TempReg('val')
			),
		InstrSem(	# str r1, [y]
			TempReg('val') << Register('r1'),
			Location('y') << TempReg('val')
			)
		)

	P2 = SeqSem(
		DoWhile(		# L:
			SeqSem(
			InstrSem(	# ldr r2, [y]
				TempReg('val') << Location('y'),
				Register('r2') << TempReg('val')
				),
			InstrSem(	# cmp r2, #1
				ParallelSem(
					TempReg('rd') << 1,
					TempReg('rt') << Register('r2')
				),
				ParallelSem(
					Register('z') << i_if_exp(TempReg('rd') == TempReg('rt'), 1, 0),
					Register('n') << i_if_exp(TempReg('rd') == TempReg('rt'), 0, 1),
				)
			)),
			((Location('x') == 0) | (Location('x') == 1)) &
			((Location('y') == 0) | (Location('y') == 1)) &
			((Register('r2') == 0) | (Register('r2') == 1)),						# { inv }
			Register('z') == 0,			# bne L
			Register('r2') == 1			# { Q }
		), 
		InstrSem(	# ldr r3, [x]
			TempReg('val') << Location('x'),
			Register('r3') << TempReg('val')
			),
		Assertion(Register('r3') == 1)
		)
	P1 = invExtractor(P1, [Register('r2')])
	P2 = invExtractor(P2, [Register('r2'), Register('r3'), Register('z'), Register('n'), Location('x'), Location('y')])

	for i in P1:
		# print i
		for j in P2:
			# print j
			break
		break
		# print i
	print '----- ssa -----'
	ssa_i = SSASem(i).ssa()
	ssa_j = SSASem(j).ssa()
	print ssa_i
	# print ssa_j
	f = encode(ssa_i)
	print f


if __name__ == '__main__':
	mp()



