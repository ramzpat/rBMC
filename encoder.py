
import ssa as SSA, norm as Norm

# Abstract Model
from HWModel.sc_model import *
# ARM Model
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
	info = encode(norm)						# program information (consists of InfoS and BasisS)
	# initial location axioms are included in BasisS
	initalLoc = modelAx.initial_location(info['Loc'])	# initial value of every location
	axioms 	= modelAx.axioms(info) 			# BasisS + X_M (constraints of a memory model)
	# U_S : Underlying behaviors
	addition = modelAx.additional_axioms(	# Additional (xo, return_value)
										Loc = info['Loc'], 
		  								MemOp = { 
		  									'read': info['MemOp']['read'],
		  									'write': info['MemOp']['write'],
		  									'rmw': info['MemOp']['rmw'] },
		  								Proc = info['Proc']) 
	behaviors = And(info['InfoS'] + info['BasisS'])		# 	CS
	properties = (And(info['PS']))	#	PS

	return (info, And(axioms + initalLoc + addition + [behaviors,Not(properties)]))



import translator

if __name__ == '__main__':
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

	  	r0, r1, r2, r3 = Consts('read_0 read_1 read_2 read_3', ReadOp)
	  	print m[WriteOp]
	  	print m[ReadOp]

	  	print m.evaluate(return_val(r0))
	  	print m.evaluate(return_val(r1))
	  	print m.evaluate(return_val(r2))
	  	print m.evaluate(return_val(r3))


		j = j + 1

	pass