
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
	assert(isinstance(e, Exp) or isinstance(e, Register) or type(e) == int or type(e) == bool)
	# print 'hey',herd.Int(str(e))
	if type(e) == int or type(e) == bool:
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
			# val := (cond)?1:0
			(cond, info) = encodeElement(i.exp.cond, info)
			(tExp, info)= encodeElement(i.exp.t_exp, info)
			(fExp, info) = encodeElement(i.exp.f_exp, info)
			info['CS'] += [ Implies(cond, var == tExp), 
							Implies(Not(cond), var == fExp) ]
	elif isinstance(i, fenceStm):
		pass 
	elif isinstance(i, branchOp):
		pass 
	return (encodeOp, formulas, info)

# result a set of formulas ?
def encode(P = [], initLocation = {}):

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
			# print cs, 'test'
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
			# try:
			if len(poRet) > 0:
				poRet = [ (pl, poRet[0][0]) for pl in prev] + poRet
			# except IndexError:
			# 	print 'Bug', prev, poRet, p
				
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

	if len(info['Ev']) > 1:
		info['CS'] += [herd.Distinct(info['Ev'])]
		# print 'hey'
	if len(info['Loc']) > 1:
		info['CS'] += [herd.Distinct(info['Loc'].values())]
	
	# initial location = 0 ?
	# print [herd.new_write(v, 0, 0) for v in info['Loc'].values() if not (str(v) in initLocation.keys())]
	# print initLocation.values()
	WriteInit = [herd.new_write(v, 0, 0) for v in info['Loc'].values() if not (str(v) in initLocation.keys())]
	WriteInit += initLocation.values()
	PoS += [ (w, p) for (p,p2) in PoS for w in WriteInit]
	info['Ev'] += WriteInit

	# print info['Ev']

	s = herd.Solver()

	s.add(herd.And(info['CS']))
	# print info['CS']
	# print 'CS', herd.simplify(herd.And(info['CS'][2:]))

	# execution
	(s, po, poS) = herd.program_order(s, PoS, info['Ev'])
	# print poS
	#  - co : W x W relation
	(s, co) = herd.conflict_order(s, info['Ev'])
	#  - rf : W x R relation
	(s, rf) = herd.read_from(s, info['Ev'])
	#  - fr : E x E relation
	(s, fr) = herd.from_read(s, rf, co)

	# Instruction semantics level
	#  - iico : E x E relation
	# print info['iico']
	(s, iico, iicoSet) = herd.iico_relation(s, info['iico'], info['Ev'])
	#  - rf-reg : W-reg x R-reg relation
	(s, rf_reg, rf_regSet) = herd.rf_reg_relation(s, info['Ev'])


	s = herd.sc_constraints(s, po, rf, fr, co, info['Ev'])
	# s = herd.tso_constraints(s, po, poS, rf, fr, co, info['Ev'])
	# s = herd.pso_constraints(s, po, poS, rf, fr, co, info['Ev'])

	print '------ PS'
	# print simplify(herd.Not(herd.And(info['PS'])))
	s.add(simplify(herd.Not(herd.And(info['PS']))))
	result = s.check()
	
	# print result
	if result == sat:
		m = s.model()
		for r in [r for r in info['Ev'] if herd.isReadReg(r)]:
			for w in [w for w in info['Ev'] if herd.isWriteReg(w) ]:
				if herd.is_true(m.evaluate(rf_reg(w,r))):
					print r, w, m.evaluate(r.val)
	return (result, s, info)

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
			((Register('z') == 0) | (Register('z') == 1)) &
			((Register('n') == 0) | (Register('n') == 1)) &
			((Register('r2') == 0) | (Register('r2') == 1)) 
			# ((Register('r3') == 0) | (Register('r3') == 1)) 
			,						# { inv }
			Register('z') == 0,			# bne L
			Register('z') == 1			# { Q }
		), 
		InstrSem(	# ldr r3, [x]
			TempReg('val') << Location('x'),
			Register('r3') << TempReg('val')
			),
		Assertion(Register('r3') == 1)
		)

	# print P2
	# havoc should analyze inside the loop!!
	P1 = invExtractor(P1, [Register('r2')])
	P2 = invExtractor(P2, [Register('r2'), Register('z'), Register('n')])
	# P3 = invExtractor(P3, [Register('r2')], P3.__class__)
	# print '---- inv'

	# for j in P2:
	# 	print j
	# 	print '-------'

	for i in P1:
		# print i
		for j in P2:
			herd.reset_id()
			ssa_i = SSASem(i).ssa()
			ssa_j = SSASem(j).ssa()
			# print ssa_j

			(result, s, info) = encode([ssa_i, ssa_j])
			# break
			if result == sat:
				break
	print result
	
def twoLoops():
	# mov r1, #0 		# counter
	# mov r2, #1		# flag
	# L:
	# str r1, [x]		# [x] := r1
	# add r1, r1, #1	# r1 := r1 + 1
	# cmp r1, #10		
	# bne r1, L  		# r1 != 10, {inv: 0 <= [x] < 10 and 0 <= r1 < 10 }, {Q: r1 == 10}
	# str r2, [y] 		# [y] := r2

	# L2:
	# 	ldr r3, [y]
	# 	cmp r3, #1
	# bne L2			# r3 != 1, {inv: r3 = {0, 1}}, {Q: r3 == 1}
	# ldr r4, [x]
	# assert()


	P1 = SeqSem(
		InstrSem(	# mov r1, #0
			TempReg('val') << 0, 
			Register('r1') << TempReg('val')
			),
		InstrSem(	# mov r2, #1
			TempReg('val') << 1, 
			Register('r2') << TempReg('val')
			),
		DoWhile(
			SeqSem(
				InstrSem(	# str r1, [x]
					TempReg('val') << Register('r1'),
					Location('x') << TempReg('val')
					),
				InstrSem(	# add r1, r1, #1
					TempReg('val') << Register('r1'),
					TempReg('val') << (TempReg('val') + 1),
					Register('r1') << TempReg('val')	
					),
				InstrSem(	# cmp r1, #10
					ParallelSem(
						TempReg('rd') << 1,
						TempReg('rt') << Register('r1')
					),
					ParallelSem(
						SeqSem(
							TempReg('val1') << ifExp(TempReg('rd') == TempReg('rt'), 1, 0),
							Register('z') << TempReg('val1')),
						SeqSem(
							TempReg('val1') << ifExp(TempReg('rd') == TempReg('rt'), 0, 1),
							Register('n') << TempReg('val1'))
					)
					)
				),
				( 
					((Location('x') >= 0) & (Location('x') <= 9)) & 
					((Register('r1') >= 0) & (Register('r1') <= 10))
				), # inv
				(Register('r1') < 10), # cond
				(Register('r1') >= 10)  # Q
			),
		
		InstrSem(	# str r2, [y]
			TempReg('val') << Register('r2'),
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
			# ((Location('x') >= 0) | (Location('x') < 10)) &
			# ((Location('y') == 0) | (Location('y') == 1)) &
			((Register('z') == 0) | (Register('z') == 1)) &
			((Register('n') == 0) | (Register('n') == 1)) &
			((Register('r2') == 0) | (Register('r2') == 1)) 
			# ((Register('r3') == 0) | (Register('r3') == 1)) 
			,						# { inv }
			Register('z') == 0,			# bne L
			Register('z') == 1			# { Q }
		), 
		InstrSem(	# ldr r3, [x]
			TempReg('val') << Location('x'),
			Register('r3') << TempReg('val')
			),
		Assertion(Register('r3') == 9)
		)

	# print P2
	# havoc should analyze inside the loop!!
	P1 = invExtractor(P1, [Register('r1'), Location('x'), Register('z'), Register('n')])
	P2 = invExtractor(P2, [Register('r2'), Register('z'), Register('n')])
	# P3 = invExtractor(P3, [Register('r2')], P3.__class__)
	# print '---- inv'
	for i in P1:
		# print i
		for j in P2:
			herd.reset_id()
			ssa_i = SSASem(i).ssa()
			ssa_j = SSASem(j).ssa()
			# print ssa_i
			# print ssa_j

			(result, s, info) = encode([ssa_i, ssa_j])
			if result == sat:
				break
		if result == sat:
			print ssa_i
			print ssa_j
			print result
			return 
			# print ssa_j
			# m = s.model()
			# for r in [r for r in info['Ev'] if herd.isRead(r)]:
			# 	for w in [w for w in info['Ev'] if herd.isWrite(w) ]:
			# 		if herd.is_true(m.evaluate(herd.rf(w,r))):
			# 			print r, w, m.evaluate(r.val)
	print result

	
def dekker():
	# 	mov r1, #1		; true
	# 	mov r2, #0		; false
	# 	mov r5, #2		; j
	# Lock: 
	# 	str r1, [xi]	; x[i] = true
	# While: 			; while(x[j]){
	# 	ldr r3, [xj]	; 	x[j] (load to r3)
	# 	cmp r3, #1		; 	x[j] = true ?
	# 	assume(r3 <> #1)	; assume HERE*********
	# 	bne CS			; 	!(x[j] = true) -> goto critical section
	# If: 			; 	if( k == j(#2) )
	# 	ldr r4, [k]		; 		k (load to r4)
	# 	cmp r4, r5		;		k = j ?
	# 	bne While  		; 		!(k = j) -> goto While
	# 	str r2, [xi]	;		x[i] = false
	# While2:			; 		while( k == j); ?
	# 	ldr r4, [k]		;			k (load to r4)
	# 	cmp	r4, r5		;			k = j ?
	# 	beq While2		;			(k = 2) -> goto While2
	# 	str r1, [xi]	;		x[i] = true
	# 	b While 		; 	goto While
	# 	CS:				; critical section:
	
	outer_inv = (
					((Location('xi') == Register('false')) | (Location('xi') == Register('true'))) & 
					((Location('xj') == Register('false')) | (Location('xj') == Register('true')))
				)
	inner_inv = (Location('turn') == 1) | (Location('turn') == 2)
	inner_Q = (~ (Location('turn') == Register('r5')))
	outer_Q = (True) 


	# eventually enter critical section 
	P1 = SeqSem(
		InstrSem(	# mov r1, #1	(true)
			TempReg('val') << 1, 
			Register('true') << TempReg('val')
			),
		InstrSem(	# mov r2, #0	(false)
			TempReg('val') << 0, 
			Register('false') << TempReg('val')
			),
		InstrSem(	# mov r5, #2	(j)
			TempReg('val') << 2, 
			Register('r5') << TempReg('val')
			),
		InstrSem(	# str true, [xi]
			TempReg('val') << Register('true'), 
			Location('xi') << TempReg('val')
			),
		# Assume((Location('xj') == 0) ),
		# IfStm((Location('xj') == 1),
		# 	DoWhile(
		# 		IfStm(~(Location('turn') == 1),
		# 		SeqSem(
		# 			InstrSem(	# str false, [xi]
		# 				TempReg('val') << Register('false'), 
		# 				Location('xi') << TempReg('val')
		# 			),
		# 			DoWhile(SeqSem(),
		# 				(inner_inv),
		# 				(~(Location('turn') == 1)),
		# 				(inner_Q)
		# 			),
		# 			InstrSem(	# str true, [xi]
		# 				TempReg('val') << Register('true'), 
		# 				Location('xi') << TempReg('val')
		# 			),
		# 			# Assume((Location('xj') == 1))
		# 			),		
		# 		# )
		# 		),
		# 	(outer_inv), # inv
		# 	((Location('xj') == 1)), # cond
		# 	(outer_Q)  # Q
		# 	),
		# ),
		# Assume((Location('xj') == 0) ),
		# Critical Section
		# InstrSem(	# str j, [turn]
		# 		TempReg('val') << Register('r5'), 
		# 		Location('turn') << TempReg('val')
		# 	),
		# InstrSem(	# str false, [xi]
		# 	TempReg('val') << Register('false'), 
		# 	Location('xi') << TempReg('val')
		# 	),
		)

	P2 = SeqSem(
		InstrSem(	# mov r1, #1	(true)
			TempReg('val') << 1, 
			Register('true') << TempReg('val')
			),
		InstrSem(	# mov r2, #0	(false)
			TempReg('val') << 0, 
			Register('false') << TempReg('val')
			),
		InstrSem(	# mov r5, #1	(j)
			TempReg('val') << 1, 
			Register('r5') << TempReg('val')
			),
		InstrSem(	# str true, [xj]
			TempReg('val') << Register('true'), 
			Location('xj') << TempReg('val')
			),
		IfStm((Location('xi') == 1),
			DoWhile(
				IfStm(~(Location('turn') == 2),
				SeqSem(
					InstrSem(	# str false, [xj]
						TempReg('val') << Register('false'), 
						Location('xj') << TempReg('val')
					),
					DoWhile(SeqSem(),
						(inner_inv),
						(~(Location('turn') == 2)),
						((Location('turn') == 2))
					),
					InstrSem(	# str true, [xj]
						TempReg('val') << Register('true'), 
						Location('xj') << TempReg('val')
					)),		
				# )
				),
			(outer_inv), # inv
			((Location('xi') == 1)), # cond
			(~(Location('xi') == 1))  # Q
			),
		),
		# Assume(Location('xi') != 1),
		Assertion(False)
		# Assertion(Location('xi') != 1),
		# Critical Section
		# InstrSem(	# str j, [turn]
		# 		TempReg('val') << Register('r5'), 
		# 		Location('turn') << TempReg('val')
		# 	),
		# InstrSem(	# str false, [xj]
		# 	TempReg('val') << Register('false'), 
		# 	Location('xj') << TempReg('val')
		# 	),
		)




	# print P2
	# havoc should analyze inside the loop!!
	P1 = invExtractor(P1, [Register('r1'), Location('x'), Register('z'), Register('n')])
	# o = 0
	# for i in P1:
	# 	ssa_i = SSASem(i).ssa()
	# 	print ssa_i
	# 	o += 1
	# 	print '----------'
	# print o
	# return 
	P2 = invExtractor(P2, [Register('r2'), Register('z'), Register('n')])
	# P3 = invExtractor(P3, [Register('r2')], P3.__class__)
	# print '---- inv'
	# for j in P2:
	# 	print j
	# 	print '--------'

	# return
	for i in P1:
		# print i
		for j in P2:
			# print j
			# result = unsat
			# continue
			herd.reset_id()
			ssa_i = SSASem(i).ssa()
			ssa_j = SSASem(j).ssa()
			# print ssa_i
			# print ssa_j
			# result = sat
			# break
			n = FreshInt()
			turn = Int('turn')
			l_turn = herd.InitLoc(turn)
			# (result, s, info) = encode([ssa_i, ssa_j])

			(result, s, info) = encode([ssa_i, ssa_j], 
									{'loc(turn)':(herd.new_write(l_turn, n, 0))})
			s.add(Or(n == 1, n == 2))
			if result == sat:
				break
		if result == sat:
			print ssa_i
			print ssa_j
			print result
			return 
			# print ssa_j
			# m = s.model()
			# for r in [r for r in info['Ev'] if herd.isRead(r)]:
			# 	for w in [w for w in info['Ev'] if herd.isWrite(w) ]:
			# 		if herd.is_true(m.evaluate(herd.rf(w,r))):
			# 			print r, w, m.evaluate(r.val)
	print result


if __name__ == '__main__':
	mp()
	# twoLoops()
	# dekker()
	pass



