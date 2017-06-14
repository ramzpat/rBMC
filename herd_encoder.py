
from Arch.arch_object import *
from HWModel.OperatorSem import *

import HWModel.herd_framework as herd
from herd_ssa import *

locationAddr = []

MemOp = []

def encodeExp(exp, info):
	if isinstance(exp, int) or isinstance(exp, bool):
		return exp
	elif isinstance(exp, Register):
		return herd.Const(str(exp), herd.Val)
	elif isinstance(exp, Exp):
		# print exp
		if(len(exp) > 2):
			op = exp[1]
			(e1,info) = encodeElement(exp[0], info)
			(e2,info) = encodeElement(exp[2], info)

			if op == EOpr['plus']:
				return e1 + e2
			elif op == EOpr['minus']:
				return e1 - e2
			elif op == EOpr['times']:
				return e1 * e2
			elif op == EOpr['divide']:
				return e1 / e2
			elif op == EOpr['eq']:
				return (e1 == e2)
			elif op == EOpr['lt']:
				return e1 < e2
			elif op == EOpr['gt']:
				return e1 > e2
			elif op == EOpr['and']:
				return herd.And(e1, e2)
			elif op == EOpr['or']:
								
				return herd.Or(e1, e2)
		elif len(exp) == 2:
			if exp[0] == EOpr['not']:
				(e1, info) = encodeElement(exp[1], info)
				return herd.Not(e1)
		else:
			return encodeElement(exp[0], info)


# def encodeMemOp(p):
# 	assert(isinstance(p, SeqSem) or isinstance(p, iSem))
# 	if isinstance(p, iSem):
# 		return encodeISem(p)
# 	elif isinstance(p, ParallelSem):
def encodeElement(e, info):
	assert(isinstance(e, Exp) or isinstance(e, Register) or type(e) == int)
	# print 'hey',herd.Int(str(e))
	if type(e) == int:
		return (e, info)
	elif isinstance(e, TempReg):
		return (herd.Int(str(e)), info)
	elif isinstance(e, Register):
		if not(str(e) in info['Reg'].keys()):
			info['Reg'][str(e)] = herd.Reg(info['RegCnt'])
			info['RegCnt'] += 1
		return (info['Reg'][str(e)], info)
	elif isinstance(e, Location):
		if not(e.address in info['Loc'].keys()):
			addrLoc = herd.Int(str(e.address))
			info['Loc'][e.address] = herd.InitLoc(addrLoc)
		return (info['Loc'][e.address], info)
	elif isinstance(e, ifExp):
		# val := (cond)?1:0
		# r1 << val 
		return (None, info)
	elif isinstance(e, undefinedExp):
		return (herd.FreshInt(), info)
	elif isinstance(e, Exp):
		return (encodeExp(e,info), info)

	return (None, info)

def encodeOpr(i, info):
	assert(isinstance(i, Operation))
	formulas = []
	encodeOp = None 
	pid = info['Pid']
	if isinstance(i, WriteAssn):		
		# herd_element
		(var, info) = encodeElement(i.var, info)
		(exp, info) = encodeElement(i.exp, info)
		# print i
		encodeOp = herd.new_write(var, exp, pid)
		
	elif isinstance(i, ReadAssn):
		# herd_element
		(var, info) = encodeElement(i.var, info)
		(exp, info) = encodeElement(i.exp, info)
		encodeOp = herd.new_read(exp, var, pid)
	elif isinstance(i, Assignment):
		(var, info) = encodeElement(i.var, info)
		if not isinstance(i.exp, ifExp):
			(exp, info) = encodeElement(i.exp, info)
			info['CS'] += [var == exp]
		else:
			pass
	elif isinstance(i, fenceStm):
		pass 
	elif isinstance(i, branchOp):
		pass 
	return (encodeOp, formulas, info)

# result a set of formulas ?
def encode(P = []):

	def constructPO(p, prev = [], info = {}):
		if isinstance(p, Assertion):
			# print 'assertion:::'
			# print p.cond
			(ps,info) = encodeElement(p.cond, info)
			info['PS'] += [ps]
			
			return ([],prev, info)
		elif isinstance(p, Assume):
			(cs,info) = encodeElement(p.cond, info)
			info['CS'] += [cs]
			return ([],prev, info)
		elif isinstance(p, Operation):

			# encode each operation... 
			(encodeOp, formulas, info) = encodeOpr(p, info)

			# prepare program order 
			ret = []
			if encodeOp:
				for i in prev:
					ret += [(i, encodeOp)]

			# prepare a set of operations
			if encodeOp:
				info['Ev'] += [encodeOp]	

			retE = [encodeOp] if encodeOp else prev
			return (ret, retE, info)
		elif isinstance(p, ParallelSem):
			poRet = []
			lastEle = []
			for pl in p.list():
				(po,e, info) = constructPO(pl, prev, info)
				lastEle += e 
				poRet += po
			return (poRet, lastEle, info)
		elif isinstance(p, InstrSem):
			poRet = []
			iico = []
			# print prev
			prev2 = []
			for pl in p.list():
				(po,e,info) = constructPO(pl, prev2, info)
				poRet += po
				prev2 = e

			info['iico'] += poRet
			# print prev, poRet[0][0]
			poRet = [ (pl, poRet[0][0]) for pl in prev] + poRet
				
			return (poRet, e, info)
		elif isinstance(p, SeqSem):
			poRet = []
			for pl in p.list():
				(po,e,info) = constructPO(pl, prev, info)
				
				poRet += po
				prev = e 

			return (poRet, prev, info)
		assert(False)

	def constructIICO(p):
		ret = []
		if isinstance(p, InstrSem):
			(iico, e, info) = constructPO(p)
			ret += iico 
		elif isinstance(p, SeqSem):
			for i in p.list():
				ret += constructIICO(i)
		return ret

	# derive the set of events
	# events = [e for e in p]
	Ev = []

	info = {
		'CS':[],
		'PS':[],
		'Ev':[],
		'iico':[],
		'Pid':0,

		'EventCnt':0,
		'RegCnt':0,
		'Reg':{},
		'Loc':{},
	}

	# collect po, iico, Events(R,W,regRW)
	# locations, facts assignment
	# properties

	# change p to be operation in z3 wrt to structure...
	PoS = []
	info['Pid'] = 1
	for p in P:
		(poS, e, info) = constructPO(p, [], info)
		PoS += poS
		info['Pid'] += 1

	info['CS'] += [herd.Distinct(info['Ev'])]
	info['CS'] += [herd.Distinct(info['Loc'].values())]
	
	# initial location = 0 ?
	WriteInit = [herd.new_write(v, 0, 0) for v in info['Loc'].values()]
	PoS += [ (w, p) for (p,p2) in PoS for w in WriteInit]
	info['Ev'] += WriteInit

	print info['Ev']

	s = herd.Solver()

	s.add(herd.And(info['CS']))

	# execution
	(s, po, poS) = herd.program_order(s, PoS, info['Ev'])
	#  - co : W x W relation
	(s, co) = herd.conflict_order(s, info['Ev'])
	#  - rf : W x R relation
	(s, rf) = herd.read_from(s, info['Ev'])
	#  - fr : E x E relation
	(s, fr) = herd.from_read(s, rf, co)

	# Instruction semantics level
	#  - iico : E x E relation
	(s, iico, iicoSet) = herd.iico_relation(s, info['iico'], info['Ev'])
	#  - rf-reg : W-reg x R-reg relation
	(s, rf_reg, rf_regSet) = herd.rf_reg_relation(s, info['Ev'])


	s = herd.sc_constraints(s, po, rf, fr, co, info['Ev'])
	# s = herd.tso_constraints(s, po, rf, fr, co, info['Ev'])
	# s = herd.pso_constraints(s, po, rf, fr, co, info['Ev'])

	print '------ PS'
	print herd.Not(herd.And(info['PS']))
	s.add(herd.Not(herd.And(info['PS'])))
	result = s.check()
	print result

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
					SeqSem(
						TempReg('val1') << ifExp(TempReg('rd') == TempReg('rt'), 1, 0),
						Register('z') << TempReg('val1')),
					SeqSem(
						TempReg('val1') << ifExp(TempReg('rd') == TempReg('rt'), 0, 1),
						Register('n') << TempReg('val1'))
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

	print P2
	P1 = invExtractor(P1, [Register('r2')])
	P2 = invExtractor(P2, [Register('r2'), Register('r3'), Register('z'), Register('n'), Location('x'), Location('y')])
	# P3 = invExtractor(P3, [Register('r2')], P3.__class__)
	print '---- inv'
	for i in P1:
		# print i
		for j in P2:
			# print j
			break
		break
		# print i
	print '----- ssa -----'
	# ssa_i = SSASem(i).ssa()
	# return 
	ssa_j = SSASem(j).ssa()
	# print ssa_i
	# print ssa_j

	print '------ encode ------'
	# f = encode([ssa_i, ssa_j])
	# print f
	# print InstrSem(	# cmp r2, #1
	# 			ParallelSem(
	# 				TempReg('rd') << 1,
	# 				TempReg('rt') << Register('r2')
	# 			),
	# 			ParallelSem(
	# 				SeqSem(
	# 					TempReg('val1') << ifExp(TempReg('rd') == TempReg('rt'), 1, 0),
	# 					Register('z') << TempReg('val1')),
	# 				SeqSem(
	# 					TempReg('val1') << ifExp(TempReg('rd') == TempReg('rt'), 0, 1),
	# 					Register('n') << TempReg('val1'))
	# 			)
	# 		)
	

if __name__ == '__main__':
	mp()



