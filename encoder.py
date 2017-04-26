
import ssa as SSA, norm as Norm

# Abstract Model
from HWModel.sc_model import *
# ARM Model
from Arch.ARM.arm_object import *
from Arch.ARM.semantics import *
# from HWModel.iSem import *

import Arch.ARM.Models.models  as arm_models

# SPARC Model
import Arch.SPARC.Models.models as sparc_models

import HWModel.encode_z3

__archList = ['arm']
__modelList = ['SC', 'TSO']

def normalize(P, arch = 'arm'):
	ssa = SSA.translate(P)
	norm = []
	for s in ssa:
		norm += [Norm.Norm(s)]
	return norm

def archEncode(P, arch = 'arm', model = 'SC'):
	# normalize
	norm = normalize(P, arch)
	modelAx = None
	if arch == 'arm':
		modelAx = arm_models.getModel(model)
		modelAx = sparc_models.getModel(model)
	else:
		modelAx = sparc_models.getModel(model)

	# encode
	info = encode(norm)				# program information

	axioms 	= modelAx.axioms(info) 			# basis axioms
	initalLoc = modelAx.initial_location(info['Loc'])	# initial value of every location
	addition = modelAx.additional_axioms(	# Additional (xo, return_value)
										Loc = info['Loc'], 
		  								MemOp = { 
		  									'read': info['MemOp']['read'],
		  									'write': info['MemOp']['write'],
		  									'rmw': info['MemOp']['rmw'] },
		  								Proc = info['Proc']) 
	behaviors = And(info['CS'])		# 	CS
	properties = (And(info['PS']))	#	PS

	return (info, And(axioms + initalLoc + addition + [behaviors,Not(properties)]))



import translator


def analyzeInstr(p):
	def isWriteAssn(i):
		if i:
			addr = i.var
			return isinstance(i, Assignment) and isinstance(addr, Location)
		return False
	for i in p:
		if isinstance(i, Assignment):
			print i
			# print str(i) + ':' + str(isWriteAssn(i))

if __name__ == '__main__':

	p1 = [
	ARMInstr(ARMInstr.mov, ARMCond.al, ARMReg.r1, int(0)),	#x
	ARMInstr(ARMInstr.mov, ARMCond.al, ARMReg.r2, int(1)),	#y
	ARMInstr(ARMInstr.mov, ARMCond.al, ARMReg.r3, int(1)),
	ARMInstr(ARMInstr.str, ARMCond.al, ARMReg.r3, Location(ARMReg.r1 + 1)),
	ARMInstr(ARMInstr.str, ARMCond.al, ARMReg.r3, Location(ARMReg.r2)),
	]

	p2 = [
	ARMInstr(ARMInstr.mov, ARMCond.al, ARMReg.r1, int(0)),	#x
	ARMInstr(ARMInstr.ldr, ARMCond.al, ARMReg.r3, Location(ARMReg.r1 + 1)),
	ARMInstr(ARMInstr.ldr, ARMCond.al, ARMReg.r4, Location(ARMReg.r1)),
	]

	sP1 = getARMSemantics(p1)
	sP2 = getARMSemantics(p2)
	# printSemantics(sP1)
	# print sP1
	# printSemantics(sP2)

	# print SSA.SSASem(sP2).ssa()

	ssaP1 = SeqSem(
		# mov r1, 0
		SeqSem(
			TempReg('result_0') << int(0),
			TempReg('r1_0') << TempReg('result_0')
		),
		# mov r2, 1
		SeqSem(
			TempReg('result_1') << int(1),
			TempReg('r2_0') << TempReg('result_1')
		),
		# str r2, [r1]
		SeqSem(
			ParallelSem(
				TempReg('addr_0') << TempReg('r1_0'),
				TempReg('val_0') << TempReg('r2_0')
			),
			Location(TempReg('addr_0')) << TempReg('val_0')
		),
		# str r2, [r1+1]
		SeqSem(
			ParallelSem(
				TempReg('addr_1') << TempReg('r1_0') + int(1),
				TempReg('val_1') << TempReg('r2_0')
			),
			Location(TempReg('addr_1')) << TempReg('val_1')
		)
	)

	ssaP2 = SeqSem(
		# mov r1, 0
		SeqSem(
			TempReg('result_1') << int(0),
			TempReg('r1_1') << TempReg('result_1')
		),
		# ldr r3, [r1+1]
		SeqSem(
			TempReg('addr_2') << TempReg('r1_1') + 1,
			TempReg('result_2') << Location(TempReg('addr_2')),
			TempReg('r3_0') << TempReg('result_2')
		),
		# ldr r4, [r1]
		SeqSem(
			TempReg('addr_3') << TempReg('r1_1'),
			TempReg('result_3') << Location(TempReg('addr_3')),
			TempReg('r4_0') << TempReg('result_3')
		)
	)
	ssaP = ParallelSem(ssaP1, ssaP2)
	print ssaP


if __name__ == '__main2__':
	# Find out counter example of TSO and reasoning the axioms for using in SMT solver 
	# P1
	# A = 1
	# u = A 
	# w = B
	# P2
	# B = 1
	# v = B  
	# x = A 
	# (u,v,w,x) = (1,1,0,0), this result is allowed in TSO
	P1 = '''
	mov r1, #1
	str r1, [X]
	ldr r2, [X]
	ldr r3, [Y]
	assert( r3 = #1 )
	'''
	P2 = '''
	mov r1, #1
	str r1, [Y]
	ldr r4, [Y]
	ldr r5, [X]
	assume( r5 = #0 )
	'''

	U = translator.translate([P1,P2])
	j = 1
	for u in U:
		# possible sets of programs 
		print '========== [ Test set #%02d ] ==========='%(j)
		norm = normalize(u)
		
		# Encoder ---------------- 
		(info,axioms) = archEncode(u)


		# Verifier 
		s = Solver()
		s.add(axioms)
	  	result = s.check()
	  	print result


	  	# print addition
	  	m = s.model()

	 #  	w0, w1 = Consts('write_0 write_1', WriteOp)
	  	r0, r1, r2, r3 = Consts('read_0 read_1 read_2 read_3', ReadOp)
	 #  	reg3 = Const('r3_0', IntSort())
	 #  	P0, P1 = Consts('P0 P1', Proc)
	  	print m[WriteOp]
	  	print m[ReadOp]

	  	print m.evaluate(return_val(r0))
	  	print m.evaluate(return_val(r1))
	  	print m.evaluate(return_val(r2))
	  	print m.evaluate(return_val(r3))


		j = j + 1

	pass