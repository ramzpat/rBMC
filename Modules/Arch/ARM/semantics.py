

if __package__ is None:	
    import sys
    from os import path
    sys.path.append( path.dirname(path.dirname( path.dirname( path.abspath(__file__) ) ) ))
    from Arch.Abstract.semantics import constructCFG as semanticsARM
    from Arch.ARM.arm_object import *
    # from HWModel.iSem import *
else:
	
	from Arch.Abstract.semantics import constructCFG as semanticsARM
	from Arch.ARM.arm_object import *
	# from HWModel.iSem import *

# focus on ARMv7

def __condSemantics__(cond, sem):
	def decode(cond):
		if cond == ARMCond.eq:
			return ((ARMReg.z) == int(1))

		if cond == ARMCond.ne:
			return ((ARMReg.z) == int(0))
		return False

	if cond == ARMCond.al:
		return [sem]
	else:
		return [ifSem(decode(cond), sem)]

def __ldrSemantics__(*operands):
	# assert False
	cond = operands[0]
	reg = operands[1]
	loc = operands[2]

	sem = []
	sem += [ Exp('address') << loc.address ] 						# realized location address (compute exp)
	sem += [ ReadAssn(Exp('resut'), Location(Exp('address'))) ]	# [read access] value of location
	sem += [ reg << Exp('resut') ]									# write back to the register
	return __condSemantics__(cond, SeqSem(*sem))

def __strSemantics__(*operands):
	cond = operands[0]
	reg = operands[1]
	reg_loc = operands[2].address
	sem = []
	sem1 = Exp('address') << reg_loc  						# read Location
	sem2 = Exp('val') << reg  								# read writting value
	sem = [ParallelSem(sem1,sem2)]
	sem += [ WriteAssn((Location(Exp('address'))), Exp('val')) ]	# write access to location
	# return [SeqSem(*sem)]
	return __condSemantics__(cond, SeqSem(*sem))

def __movSemantics__(*operands):
	cond = operands[0]
	rd = operands[1]
	rt = operands[2]
	sem = []
	sem += [Exp('result') << rt]
	sem += [rd << Exp('result')]
	return __condSemantics__(cond, SeqSem(*sem))

# add
def __addSemantics__(*operands):
	cond = operands[0]
	rd = operands[1]
	rn = operands[2]
	rm = operands[3]
	sem = []
	#	shifted = Shift(R[m], shift_t, shift_n, APSR.C);
	#	(result, carry, overflow) = AddWithCarry(R[n], shifted, '0');
	sem += [Exp('result') << rn + rm]
	sem += [rd << Exp('result')]
	return __condSemantics__(cond, SeqSem(*sem))

# sub
def __subSemantics__(*operands):
	cond = operands[0]
	rd = operands[1]
	rn = operands[2]
	rm = operands[3]

	sem = []
	sem += [Exp('result') << rn - rm]
	sem += [rd << Exp('result')]
	return __condSemantics__(cond, SeqSem(*sem))

# and
def __andSemantics__(*operands):
	return []

# b ?
def __bSemantics__(*operands):
	cond = operands[0]
	label = operands[1]

	return __condSemantics__(cond, SeqSem(gotoSem(label.label_name)))

# cmp
def __cmpSemantics__(*operands):
	cond = operands[0]
	rn = operands[1]
	rm = operands[2]
	return __condSemantics__(cond,
		ParallelSem(
			(ARMReg.z) << ifExp(rn == rm, 1, 0),
			(ARMReg.n) << ifExp(rn < rm, 1, 0)  
		)
		)

# ldrex (require atomic and reservation location)
# strex (require atomic and reservation location)


def __getInstrSemantics(instr):
	func = {
		ARMInstr.mov : __movSemantics__,
		ARMInstr.str : __strSemantics__,
		ARMInstr.ldr : __ldrSemantics__, 
		ARMInstr.cmp : __cmpSemantics__,
		ARMInstr.add : __addSemantics__, 
		ARMInstr.sub : __subSemantics__, 
		ARMInstr.b 	 : __bSemantics__
	}
	if isinstance(instr, Label):
		return [labelSem(instr.label_name)]
	elif instr.instr_name is 'dsb':
		return [ffence('dsb')]
	elif instr.instr_name is 'dmb':
		return [ffence('dmb')]
	else:
		return func[instr.instr_name](*instr.operands)
	return []

def getARMSemantics(p):
	sem = []
	for ii in p:
		sem += __getInstrSemantics(ii)
	# print sem
	return SeqSem(*sem)

if __name__ == '__main__':

	# ldreq r2, [r1]
	i1 = ARMInstr(ARMInstr.ldr, ARMCond.eq, (ARMReg.r2), Location(ARMReg.r1))
	# strne r1, [r2]
	i2 = ARMInstr(ARMInstr.str, ARMCond.al, (ARMReg.r1), Location(ARMReg.r2))
	i3 = Label('L') #ARMInstr.dsb
	i4 = ARMInstr(ARMInstr.b, ARMCond.eq, Label('L'))
	i5 = ARMInstr(ARMInstr.cmp, ARMCond.al, ARMReg.r3, ARMReg.r2)
	p = [i1, i2, i3, i4, i5]
	# for ii in p:
	# 	print ii
	print '----- semantics'
	sem = getARMSemantics(p)
	# print *sem
	# seq = SeqSem(*sem)
	print sem
	# printSemantics(getARMSemantics(p))
	
