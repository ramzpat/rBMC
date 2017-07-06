# SMT encoder


from HWModel.OperatorSem import *
from Arch.arch_object import *

from encodingFW import *
from InvExtractor import *
import gharachorloo_framework  as gFW
import herd_encodingFw as hFW 

def isVar(i):
	return isinstance(i, Register)

def ssa_form(P):
	if not isinstance(P, list):
		P = [P]

	def new_var(set_name, state):
		# state['dynamic_nickname']
		# state['dynamic_vars']
		# state['dynamic_cnt']

		if(set_name in state['dynamic_vars']):
			var_name = state['dynamic_nickname'][set_name]+'_'+str(state['dynamic_cnt'][set_name])
			state['dynamic_vars'][set_name].append(var_name)
			state['dynamic_cnt'][set_name] = state['dynamic_cnt'][set_name] + 1
			return (var_name, state)
		else:
			state['dynamic_vars'][set_name] = []
			state['dynamic_cnt'][set_name] = 0
			state['dynamic_nickname'][set_name] = set_name
			return new_var(set_name, state)

	def get_last_var(set_name, state):
		# global dynamic_nickname
		# global dynamic_vars
		# global dynamic_cnt
		if(set_name in state['dynamic_vars']):
			var_name = state['dynamic_nickname'][set_name]+'_'+str(state['dynamic_cnt'][set_name]-1)
			return var_name
		else:
			return 'undefined'	
			raise NameError('There are no variable name "' + set_name + '"')
			name, state = new_var(set_name, state)
			return  name # wrong

	def new_exp(exp, state):
		if isVar(exp):
			# print exp, exp.__class__
			clss = exp.__class__ 
			return Exp( clss(get_last_var(str(exp), state)) )
		elif isinstance(exp, ifExp):
			return ifExp( new_exp(exp.cond, state), 
							 new_exp(exp.t_exp, state),
							 new_exp(exp.f_exp, state) )
		elif isinstance(exp, Exp):
			if len(exp) > 2 and (exp[1] == EOpr['plus'] or exp[1] == EOpr['minus'] or exp[1] == EOpr['times'] or 
				exp[1] == EOpr['divide'] or exp[1] == EOpr['eq'] or exp[1] == EOpr['lt'] or exp[1] == EOpr['gt'] or
				exp[1] == EOpr['and'] or exp[1] == EOpr['or']  ):
				return Exp( new_exp(exp[0], state),
							exp[1],
							new_exp(exp[2], state))
			elif len(exp) == 2 and exp[0] == EOpr['not'] :
				return Exp(EOpr['not'],(new_exp(exp[1], state)))
			# else:
			# 	return newExp(exp[0], lastVarName)
		return exp

	def newOpr(e, state):
		assert(isinstance(e, Operation) or isinstance(e, Ops) or isinstance(e, AnnotatedStatement))
		if isinstance(e, AnnotatedStatement):
			if isinstance(e, Assertion) or isinstance(e, Assume):
				e.cond = new_exp(e.cond, state)
		elif isinstance(e, Operation):
			if isinstance(e, Assignment):
				var = e.var
				exp = e.exp 
				var_name = str(var)
				nExp = exp if (isinstance(exp, Location)) else new_exp(exp, state)
				(nVar,state) = (var.address,state) if (isinstance(var, Location)) else new_var(var_name, state)
				e.var = var.__class__(nVar)
				e.exp = nExp 
			elif isinstance(e, fenceStm):
				pass 
			elif isinstance(e, branchOp):
				pass
			else:
				assert(False)
		elif isinstance(e, Ops):
			# if isinstance(e, InstrOps):

			for i in e.elements:
				state = newOpr(i, state)

		return state 


	# [P] = self.additionalRead(P)
	def getLocations(exp):
		if isinstance(exp, Location):
			return [exp]
		elif isinstance(exp, TempReg):
			return []
		elif isinstance(exp, Register):
			return [exp]
		elif isVar(exp):
			return []
		elif isinstance(exp, Exp):
			if len(exp) > 2 and (exp[1] == EOpr['plus'] or exp[1] == EOpr['minus'] or exp[1] == EOpr['times'] or 
				exp[1] == EOpr['divide'] or exp[1] == EOpr['eq'] or exp[1] == EOpr['lt'] or exp[1] == EOpr['gt'] or
				exp[1] == EOpr['and'] or exp[1] == EOpr['or']  ):

				return getLocations(exp[0]) + getLocations(exp[2])
			elif len(exp) == 2 and exp[0] == EOpr['not'] :
				return getLocations(exp[1])
		return []

	def updateCond(exp, dictLoc):
		if isinstance(exp, Location):
			return dictLoc[exp]
		elif isinstance(exp, TempReg):
			return exp
		elif isinstance(exp, Register):
			return dictLoc[exp]
		elif isVar(exp):
			return exp
		elif isinstance(exp, Exp):
			if len(exp) > 2 and (exp[1] == EOpr['plus'] or exp[1] == EOpr['minus'] or exp[1] == EOpr['times'] or 
				exp[1] == EOpr['divide'] or exp[1] == EOpr['eq'] or exp[1] == EOpr['lt'] or exp[1] == EOpr['gt'] or
				exp[1] == EOpr['and'] or exp[1] == EOpr['or']  ):

				return Exp( updateCond(exp[0], dictLoc),
							exp[1],
							updateCond(exp[2], dictLoc))
			elif len(exp) == 2 and exp[0] == EOpr['not'] :
				return Exp(EOpr['not'],(updateCond(exp[1], dictLoc)))
		return exp

	def additionalRead(p):
		if isinstance(p, Assertion):
			locVar = getLocations(p.cond)
			locVar = set(locVar)
			dictLoc = {}

			for v in locVar:
				dictLoc[v] = TempReg('val_'+str(v.address if isinstance(v, Location) else v))
			# print self.updateCond(p, dictLoc)
			return SeqOps( *([dictLoc[v] << v for v in locVar] + [Assertion(updateCond(p.cond, dictLoc))]) )
		elif isinstance(p, Assume):
			locVar = getLocations(p.cond)
			locVar = set(locVar)
			dictLoc = {}
			for v in locVar:
				dictLoc[v] = TempReg('val_'+str(v.address if isinstance(v, Location) else v))
			# print self.updateCond(p, dictLoc)
			return SeqOps( *([ dictLoc[v] << v for v in locVar] + [Assume(updateCond(p.cond, dictLoc))]))
		elif isinstance(p, Operation):
			return p
		elif isinstance(p, SeqOps):
			new_elements = SeqOps()
			for i in p.elements:
				new_elements.append(additionalRead(i))
			return new_elements

		elif isinstance(p, ParOps):
			new_elements = ParOps()
			for i in p.elements:
				new_elements.append(additionalRead(i))
			return new_elements
		elif isinstance(p, InstrOps):
			new_elements = InstrOps()
			for i in p.elements:
				new_elements.append(additionalRead(i))
			return new_elements
		elif isinstance(p, AnnotatedStatement):
			return p
		elif isinstance(p, Ops):
			return p
		assert(False)

	def ssa_seq(P, state = {}):
		assert(isinstance(P, SeqOps))
		P = P.clone()

		P = additionalRead(P)

		for i in P.elements:
			state = newOpr(i, state)
		return (P, state)

	state = {
		'dynamic_nickname' : {},
		'dynamic_vars' : {},
		'dynamic_cnt' : {}
	}
	ssa = []
	for p in P:
		(e, state) = ssa_seq(p, state)
		ssa += [e]
	return ssa 

# return z3 formulas 
def encode(P, encoder):
	if isinstance(encoder, encodingFW):
		formulas = encoder.encode(P)
		return formulas

def mp2():
	P1 = seqOpsNode(
			InstrOps(	# mov r1, #1
				TempReg('val') << 1, 
				Register('r1') << TempReg('val')
				),
			InstrOps(	# str r1, [x]
				TempReg('val') << Register('r1'),
				Location('x') << TempReg('val')
				),
			InstrOps(	# str r1, [y]
				TempReg('val') << Register('r1'),
				Location('y') << TempReg('val')
			))

	P2 = seqOpsNode(
			LabelStm('A'),
			InstrOps(	# ldr r2, [y]
				TempReg('val') << Location('y'),
				Register('r2') << TempReg('val')
				),
			InstrOps(	# cmp r2, #1
				ParOps(
					TempReg('rd') << 1,
					TempReg('rt') << Register('r2')
				),
				ParOps(
					SeqOps(
						TempReg('val_z') << ifExp(TempReg('rd') == TempReg('rt'), 1, 0),
						Register('z') << TempReg('val_z')
					),
					SeqOps(
						TempReg('val_n') << ifExp(TempReg('rd') == TempReg('rt'), 0, 1),
						Register('n') << TempReg('val_n')
					)
				)
			),
			InstrOps(	# bne A 
				branchOp(Register('n') == 1, LabelStm('A'))
			),
			InstrOps(	# ldr r1, [x]
				TempReg('val') << Location('x'),
				Register('r1') << TempReg('val')
			),
			Assertion(Register('r1') == 1)
		)

	# SeqSem(
	# 	DoWhile(		# L:
	# 		SeqSem(
	# 			DoWhile(
	# 				InstrSem(	# ldr r2, [y]
	# 					TempReg('xal') << Location('y'),
	# 					Register('X2') << TempReg('val')
	# 					),
	# 					(Register('z') == 0),						# { inv }
	# 				Register('z') == 0,			# bne L
	# 				Register('z') == 1			# { Q }
	# 			), 

	# 		InstrSem(	# cmp r2, #1
	# 			ParallelSem(
	# 				TempReg('rd') << 1,
	# 				TempReg('rt') << Register('r2')
	# 			),
	# 			ParallelSem(
	# 				Register('z') << i_if_exp(TempReg('rd') == TempReg('rt'), 1, 0),
	# 				Register('n') << i_if_exp(TempReg('rd') == TempReg('rt'), 0, 1),
	# 			)
	# 		)),
	# 		(Register('z') == 0),						# { inv }
	# 		Register('z') == 0,			# bne L
	# 		Register('z') == 1			# { Q }
	# 	), 
	# 	InstrSem(	# ldr r3, [x]
	# 		TempReg('val') << Location('x'),
	# 		Register('r3') << TempReg('val')
	# 		),
	# 	Assertion(Register('r3') == 1)
	# 	)

	# LabelNode = OpsNode(LabelStm('A'), [])
	# BranchNode = OpsNode(
	# 					InstrOps(
	# 						branchOp(Register('r1') == 1, LabelStm('B'))
	# 					),[
	# 						OpsNode(InstrOps(	# str r1, [y]
	# 							TempReg('val') << Register('r1'),
	# 							Location('x') << TempReg('val'),
	# 							TempReg('val') << Location('x')

	# 							))
	# 						# TerminateNode()
	# 						# , LabelNode
	# 					])
	# # print P1
	# # P1 << BranchNode

	# # P1 << OpsNode(LabelStm('B'))
	# # LabelNode.next = [P1]	
	# # print dominate(LabelNode, BranchNode, LabelNode)
		
	print '+++++++'
	
	P1 = branchExtractor(P1)
	P2 = branchExtractor(P2)
	# for i in P2:
	# 	print i
	# print '*******'
	# return 
	# U = unwindLoop(LabelNode, LabelNode, 1)
	U = unrollCombination([P1, P2], 2)
	# i = 0
	for p in U:
		# print p
		[i, j] = ssa_form(p)
		# print i
		# print j
		formula = encode([i, j], gFW.encoder('SC'))
		ss = hFW.encoder('SC')
		formula = encode([i, j], ss)

		s = Solver()
		s.add(formula)
		result = s.check()
		print result
		# if result == sat:
		# 	m = s.model()
		# 	for e in ss.info['Ev']:
		# 		if hFW.isRead(e) or hFW.isReadReg(e):
		# 			print e, m.evaluate(e.val)
		# 	for e1 in ss.info['Ev']:
		# 		for e2 in ss.info['Ev']:
		# 			if is_true(m.evaluate( ss.info['rel_po'](e1,e2) )) and hFW.isRW(e2) and hFW.isRW(e1):
		# 				print e1,e2
		# 	for e1 in ss.info['Ev']:
		# 		for e2 in ss.info['Ev']:
		# 			if is_true(m.evaluate( ss.info['rel_rf'](e1,e2) )):
		# 				print e1,e2
		# 		# print m.evaluate(ss.info['rel_co']())
		# # print formula
		
		print '----'
	# print i
	# for p in P1:
	# 	print p
	# 	print '----'

def mp():
	P1 = seqOpsNode(
			InstrOps(	# mov r1, #1
				TempReg('val') << 1, 
				Register('r1') << TempReg('val')
				),
			InstrOps(	# str r1, [x]
				TempReg('val') << Register('r1'),
				Location('x') << TempReg('val')
				),
			InstrOps(	# str r1, [y]
				TempReg('val') << Register('r1'),
				Location('y') << TempReg('val')
			))

	P2 = seqOpsNode(
			LabelStm('A'),
			InstrOps(	# ldr r2, [y]
				TempReg('val') << Location('y'),
				Register('r2') << TempReg('val')
				),
			InstrOps(	# cmp r2, #1
				ParOps(
					TempReg('rd') << 1,
					TempReg('rt') << Register('r2')
				),
				ParOps(
					SeqOps(
						TempReg('val_z') << ifExp(TempReg('rd') == TempReg('rt'), 1, 0),
						Register('z') << TempReg('val_z')
					),
					SeqOps(
						TempReg('val_n') << ifExp(TempReg('rd') == TempReg('rt'), 0, 1),
						Register('n') << TempReg('val_n')
					)
				)
			),
			InstrOps(	# bne A 
				branchOp(Register('n') == 1, LabelStm('A'))
			),
			InstrOps(	# ldr r1, [x]
				TempReg('val') << Location('x'),
				Register('r1') << TempReg('val')
			),
			Assertion(Register('r1') == 1)
		)
	P1 = branchExtractor(P1)
	P2 = branchExtractor(P2)

	# for i in P2:
	# 	print i
	# return 
	U = unrollCombination([P1, P2], 1)
	for p in U:
		# print p
		[i, j] = ssa_form(p)
		# print i
		# print i
		# return
		formula = encode([i, j], gFW.encoder('SC'))
		ss = hFW.encoder('SC')
		formula = encode([i, j], ss)

		s = Solver()
		s.add(formula)
		result = s.check()
		print result
		if result == sat:
			return 
		
		print '----'

def mp_fence():
	P1 = seqOpsNode(
			InstrOps(	# mov r1, #1
				TempReg('val') << 1, 
				Register('r1') << TempReg('val')
				),
			InstrOps(	# str r1, [x]
				TempReg('val') << Register('r1'),
				Location('x') << TempReg('val')
				),
			# fence ?
			InstrOps(	# STBar 
				# hFW.STBarFence(),
				gFW.STBarFence()
				),
			InstrOps(	# str r1, [y]
				TempReg('val') << Register('r1'),
				Location('y') << TempReg('val')
			))

	P2 = seqOpsNode(
			LabelStm('A'),
			InstrOps(	# ldr r2, [y]
				TempReg('val') << Location('y'),
				Register('r2') << TempReg('val')
				),
			InstrOps(	# cmp r2, #1
				ParOps(
					TempReg('rd') << 1,
					TempReg('rt') << Register('r2')
				),
				ParOps(
					SeqOps(
						TempReg('val_z') << ifExp(TempReg('rd') == TempReg('rt'), 1, 0),
						Register('z') << TempReg('val_z')
					),
					SeqOps(
						TempReg('val_n') << ifExp(TempReg('rd') == TempReg('rt'), 0, 1),
						Register('n') << TempReg('val_n')
					)
				)
			),
			InstrOps(	# bne A 
				branchOp(Register('n') == 1, LabelStm('A'))
			),
			InstrOps(	# ldr r1, [x]
				TempReg('val') << Location('x'),
				Register('r1') << TempReg('val')
			),
			Assertion(Register('r1') == 1)
		)


	P1 = branchExtractor(P1)
	P2 = branchExtractor(P2)
	U = unrollCombination([P1, P2], 1)
	for p in U:
		# print p
		[i, j] = ssa_form(p)
		print i
		# print j
		formula = encode([i, j], gFW.encoder('PSO'))
		# ss = hFW.encoder('SC')
		# formula = encode([i, j], ss)

		s = Solver()
		s.add(formula)
		result = s.check()
		print result
		if result == sat:
			return 
		
		print '----'

def spin_SPARC():
	P1 = seqOpsNode(
			LabelStm('L1'),
			InstrOps(	# ldstub [lock], r5
				Atomic(TempReg('val') << Location('lock')), 
				Register('r5') << TempReg('val'),
				Atomic(Location('lock') << 1),
				),
			InstrOps(	# brnz, pn r5, L2
					branchOp(~ (Register('r5') == 0), LabelStm('L2')),
					# nop instr
					Ops(),
				),
			InstrOps(	# ba CS
					branchOp(True, LabelStm('CS'))
				),
			LabelStm('L2'),
			InstrOps(	# ldub [lock], r5
					TempReg('val') << Location('lock'),
					Register('r5') << TempReg('val')
				),
			InstrOps(	# brnz, pt, r5, L2
					branchOp(~ (Register('r5') == 0), LabelStm('L2')),
					# nop instr
					Ops(),
				),
			InstrOps(	# ba, a, pt, L1
					branchOp(True, LabelStm('L1')),
					# nop instr
					Ops(),	
				),
			LabelStm('CS'),
			)

	# for i in P1:
	# 	print i
	P2 = seqOpsNode(
			LabelStm('L1'),
			InstrOps(	# ldstub [lock], r5
				Atomic(TempReg('val') << Location('lock')), 
				Register('r5') << TempReg('val'),
				Atomic(Location('lock') << 1),
				),
			InstrOps(	# brnz, pn r5, L2
					branchOp(~ (Register('r5') == 0), LabelStm('L2')),
					# nop instr
					Ops(),
				),
			InstrOps(	# ba CS
					branchOp(True, LabelStm('CS'))
				),
			LabelStm('L2'),
			InstrOps(	# ldub [lock], r5
					TempReg('val') << Location('lock'),
					Register('r5') << TempReg('val')
				),
			InstrOps(	# brnz, pt, r5, L2
					branchOp(~ (Register('r5') == 0), LabelStm('L2')),
					# nop instr
					Ops(),
				),
			InstrOps(	# ba, a, pt, L1
					branchOp(True, LabelStm('L1')),
					# nop instr
					Ops(),	
				),
			LabelStm('CS'),
			)


	P1 = branchExtractor(P1)
	P2 = branchExtractor(P2)
	U = unrollCombination([P1], 0)
	for p in U:
	# 	# print p
		[i, j] = ssa_form(p)
		print i
	# 	# print j
	# 	formula = encode([i, j], gFW.encoder('PSO'))
	# 	# ss = hFW.encoder('SC')
	# 	# formula = encode([i, j], ss)

	# 	s = Solver()
	# 	s.add(formula)
	# 	result = s.check()
	# 	print result
	# 	if result == sat:
	# 		return 
		
	# 	print '----'


if __name__ == '__main__':
	# mp()
	mp_fence()
	# spin_SPARC()
