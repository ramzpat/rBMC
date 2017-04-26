
from Arch.arch_object import *
from HWModel.iSem import *

import HWModel.herd_framework

# result a set of formulas ?
def encode(p):

	def constructPOList(*p):
		p0 = p[0]
		ret = []
		for i in p[1:]:
			ret += [(p0, i)]
			p0 = i
		return ret
	
	
	def constructPO(p, prev = []):
		# if type(p) == list:
		# 	pass
		# el
		print p
		if isinstance(p, iSem):
			if len(prev):
				return [(prev[-1], p)]
			return []	
		elif isinstance(p, ParallelSem):
			ret = ([prev[-1]] if len(prev) else [])
			poRet = []
			# for pl in p.list():
				
		elif isinstance(p, SeqSem):
			ret = ([prev[-1]] if len(prev) else [])
			poRet = []
			for pl in p.list():
				poRet += constructPO(pl, ret)
			return poRet
			

	def constructIICO(p):
		return []

	# derive the set of events
	events = [e for e in p]
	
	# derive po
	po = constructPO(p)
	print po

	# derive iico



if __name__ == '__main__':

	ssaP1 = SeqSem(
		# mov r1, 0
		InstrSem(
			TempReg('result_0') << int(0),
			TempReg('r1_0') << TempReg('result_0')
		),
		# mov r2, 1
		InstrSem(
			TempReg('result_1') << int(1),
			TempReg('r2_0') << TempReg('result_1')
		),
		# str r2, [r1]
		InstrSem(
			ParallelSem(
				TempReg('addr_0') << TempReg('r1_0'),
				TempReg('val_0') << TempReg('r2_0')
			),
			Location(TempReg('addr_0')) << TempReg('val_0')
		),
		# str r2, [r1+1]
		InstrSem(
			ParallelSem(
				TempReg('addr_1') << TempReg('r1_0') + int(1),
				TempReg('val_1') << TempReg('r2_0')
			),
			Location(TempReg('addr_1')) << TempReg('val_1')
		)
	)

	ssaP2 = SeqSem(
		# mov r1, 0
		InstrSem(
			TempReg('result_1') << int(0),
			TempReg('r1_1') << TempReg('result_1')
		),
		# ldr r3, [r1+1]
		InstrSem(
			TempReg('addr_2') << TempReg('r1_1') + 1,
			TempReg('result_2') << Location(TempReg('addr_2')),
			TempReg('r3_0') << TempReg('result_2')
		),
		# ldr r4, [r1]
		InstrSem(
			TempReg('addr_3') << TempReg('r1_1'),
			TempReg('result_3') << Location(TempReg('addr_3')),
			TempReg('r4_0') << TempReg('result_3')
		)
	)
	ssaP = ParallelSem(ssaP1, ssaP2)
	# print ssaP
	f = encode(ssaP)