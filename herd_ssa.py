# SAA for new idea


from Arch.arch_object import *
from HWModel.OperatorSem import *
from InvExtractor import *

def isVar(i):
	# return isinstance(i, Register)
	return isinstance(i, TempReg)

def newExp(exp, lastVarName):
	if isVar(exp):
		clss = exp.__class__ 
		return Exp( clss(lastVarName(str(exp))) )
	elif isinstance(exp, ifExp):

		return i_if_exp( newExp(exp.cond, lastVarName), 
						 newExp(exp.t_exp, lastVarName),
						 newExp(exp.f_exp, lastVarName) )
	elif isinstance(exp, i_read):
		return exp # nothing to do with an address  -- load(Addr)
	elif isinstance(exp, i_rmw):
		return i_rmw( newExp(exp.rt, lastVarName), exp.addr )

	elif isinstance(exp, Exp):
		if len(exp) > 2 and (exp[1] == EOpr['plus'] or exp[1] == EOpr['minus'] or exp[1] == EOpr['times'] or 
			exp[1] == EOpr['divide'] or exp[1] == EOpr['eq'] or exp[1] == EOpr['lt'] or exp[1] == EOpr['gt'] or
			exp[1] == EOpr['and'] or exp[1] == EOpr['or']  ):
			return Exp( newExp(exp[0], lastVarName),
						exp[1],
						newExp(exp[2], lastVarName))
		elif len(exp) == 2 and exp[0] == EOpr['not'] :
			return Exp(EOpr['not'],(newExp(exp[1], lastVarName)))
		# else:
		# 	return newExp(exp[0], lastVarName)
	return exp

def newInstr(instr, newVarName, lastVarName):
	if isinstance(instr, i_assignment) :
		clss = instr.var.__class__
		return clss( newVarName(str(instr.var)) ) << newExp(instr.expression, lastVarName)
	elif isinstance(instr, InstrAssume): 
		return InstrAssume( newExp(instr.cond, lastVarName) )
	elif isinstance(instr, InstrAssert): 
		return InstrAssert( newExp(instr.cond, lastVarName) )
	elif isinstance(instr, i_if):
		newS = []
		for e in instr.statement:
			newS = newS + [newInstr(e, newVarName, lastVarName)]
		return i_if( newExp(instr.cond, lastVarName), newS)
	elif isinstance(instr, i_write):
		return i_write( newExp(instr.rt, lastVarName), instr.addr )

	return instr


dynamic_nickname = {}
dynamic_vars = {}
dynamic_cnt = {}

def translate(S):
	global dynamic_nickname
	global dynamic_vars
	global dynamic_cnt
	dynamic_nickname = {}
	dynamic_vars = {}
	dynamic_cnt = {}
	
	newS = []
	for s in S:
		newS += [__translate(s)]
	return newS

def __translate(s):
	def __new_var(set_name):
		global dynamic_nickname
		global dynamic_vars
		global dynamic_cnt
		if(set_name in dynamic_vars):
			var_name = dynamic_nickname[set_name]+'_'+str(dynamic_cnt[set_name])
			dynamic_vars[set_name].append(var_name)
			dynamic_cnt[set_name] = dynamic_cnt[set_name] + 1
			return var_name
		else:
			dynamic_vars[set_name] = []
			dynamic_cnt[set_name] = 0
			dynamic_nickname[set_name] = set_name
			return __new_var(set_name)

	def __get_last_var(set_name):
		global dynamic_nickname
		global dynamic_vars
		global dynamic_cnt
		if(set_name in dynamic_vars):
			var_name = dynamic_nickname[set_name]+'_'+str(dynamic_cnt[set_name]-1)
			return var_name
		else:
			# return 'undefined'	
			# raise NameError('There are no variable name "' + set_name + '"')
			return __new_var(set_name) # wrong

	newS = []
	for e in s:
		i = newInstr(e, __new_var, __get_last_var)
		newS = newS + [i]
	return newS

class SSASem:
	def __init__(self, p):
		assert(isinstance(p, SeqSem))
		self.p = p

	dynamic_nickname = {}
	dynamic_vars = {}
	dynamic_cnt = {}

	def __new_var(self, set_name):
		set_name = str(set_name)
		if(set_name in self.dynamic_vars):
			var_name = str(self.dynamic_nickname[set_name])+'_'+str(self.dynamic_cnt[set_name])
			self.dynamic_vars[set_name].append(var_name)
			self.dynamic_cnt[set_name] = self.dynamic_cnt[set_name] + 1
			return var_name
		else:
			self.dynamic_vars[set_name] = []
			self.dynamic_cnt[set_name] = 0
			self.dynamic_nickname[set_name] = set_name
			return self.__new_var(set_name)

	def __get_last_var(self, set_name):
		set_name = str(set_name)
		self.dynamic_nickname
		self.dynamic_vars
		self.dynamic_cnt

		if(set_name in self.dynamic_vars):
			var_name = str(self.dynamic_nickname[set_name])+'_'+str(self.dynamic_cnt[set_name]-1)
			return var_name
		else:
			# return 'undefined'	
			# raise NameError('There are no variable name s"' + set_name + '"')
			return self.__new_var(set_name) # wrong
	def newExp(self, exp):
		if isVar(exp):
			clss = exp.__class__ 
			return ( clss(self.__get_last_var(str(exp))) )
		elif isinstance(exp, ifExp):
			return ifExp( self.newExp(exp.cond), 
							 self.newExp(exp.t_exp),
							 self.newExp(exp.f_exp) )
		elif isinstance(exp, Exp):

			if len(exp) > 2 and (exp[1] == EOpr['plus'] or exp[1] == EOpr['minus'] or exp[1] == EOpr['times'] or 
				exp[1] == EOpr['divide'] or exp[1] == EOpr['eq'] or exp[1] == EOpr['lt'] or exp[1] == EOpr['gt'] or
				exp[1] == EOpr['and'] or exp[1] == EOpr['or']  ):

				return Exp( self.newExp(exp[0]),
							exp[1],
							self.newExp(exp[2]))
			elif len(exp) == 2 and exp[0] == EOpr['not'] :
				return Exp(EOpr['not'],(self.newExp(exp[1])))
			# else:
			# 	return newExp(exp[0], lastVarName)
		return exp

	def __ssa(self, p):
		if isinstance(p, Assertion):
			# generate read ?
			return Assertion( self.newExp(p.cond) )
		elif isinstance(p, Assume):
			# generate read ?
			return Assume( self.newExp(p.cond) )
		elif isinstance(p, WriteAssn):
			var = p.var if (isinstance(p.var, Location) or not isVar(p.var)) else p.var.__class__(self.__new_var(p.var))
			exp = p.exp
			return var << (self.newExp(exp))
		elif isinstance(p, ReadAssn):
			var = p.var
			exp = p.exp if (isinstance(p.exp, Location) or not isVar(p.exp)) else (self.newExp(p.exp))
			return p.var.__class__(self.__new_var(var)) << exp
		elif isinstance(p, Assignment) and not(isinstance(p.var, Location)):
			var = p.var
			exp = p.exp
			# if var in self.dynamic_vars:
			# 	print self.dynamic_vars[var]
			return Assignment(p.var.__class__(self.__new_var(var)), (self.newExp(exp)))
		elif isinstance(p, ParallelSem):
			newPar = []
			for i in p.list():
				newPar += [self.__ssa(i)]
			# print '---- debug parallel'
			# print p
			for i in newPar:
				print i
			# print '++++ debug parallel'
			return ParallelSem(*newPar)
		elif isinstance(p, IfStm):
			newSeq = []
			assnVars = []
			for i in p.list():
				newSeq += [self.__ssa(i)]
			# print SeqSem(*newSeq)
			return IfStm(p.cond, *newSeq)
		elif isinstance(p, SeqSem):
			newSeq = []
			# print '------ debug SeqSem'
			# print p
			for i in p.list():
				newSeq += [self.__ssa(i)]
			# print SeqSem(*newSeq)
			# print '++++++ debug SeqSem'
			return p.__class__(*newSeq)
		return p

	def eliminateHavoc(self, p):
		if isinstance(p, havoc):
			return [ v << undefinedExp() for v in p.vars]
		elif isinstance(p, ParallelSem):
			newPar = []
			for i in p.list():
				newPar += self.eliminateHavoc(i)

			return [ParallelSem(*newPar)]
		elif isinstance(p, IfStm):
			newSeq = []
			for i in p.list():
				newSeq += self.eliminateHavoc(i)
			# print SeqSem(*newSeq)
			return [IfStm(p.cond, *newSeq)]
		elif isinstance(p, SeqSem):
			newSeq = []
			for i in p.list():
				newSeq += self.eliminateHavoc(i)
			# print SeqSem(*newSeq)
			return [p.__class__(*newSeq)]
		else:
			return [p]

	def getLocations(self, exp):
		if isinstance(exp, Location):
			return [exp]
		elif isinstance(exp, Register):
			return [exp]
		elif isVar(exp):
			return []
		elif isinstance(exp, Exp):
			if len(exp) > 2 and (exp[1] == EOpr['plus'] or exp[1] == EOpr['minus'] or exp[1] == EOpr['times'] or 
				exp[1] == EOpr['divide'] or exp[1] == EOpr['eq'] or exp[1] == EOpr['lt'] or exp[1] == EOpr['gt'] or
				exp[1] == EOpr['and'] or exp[1] == EOpr['or']  ):

				return self.getLocations(exp[0]) + self.getLocations(exp[2])
			elif len(exp) == 2 and exp[0] == EOpr['not'] :
				return self.getLocations(exp[1])
		return []

	def updateCond(self, exp, dictLoc):
		if isinstance(exp, Location):
			return dictLoc[exp]
		elif isinstance(exp, Register):
			return dictLoc[exp]
		elif isVar(exp):
			return exp
		elif isinstance(exp, Exp):
			if len(exp) > 2 and (exp[1] == EOpr['plus'] or exp[1] == EOpr['minus'] or exp[1] == EOpr['times'] or 
				exp[1] == EOpr['divide'] or exp[1] == EOpr['eq'] or exp[1] == EOpr['lt'] or exp[1] == EOpr['gt'] or
				exp[1] == EOpr['and'] or exp[1] == EOpr['or']  ):

				return Exp( self.updateCond(exp[0], dictLoc),
							exp[1],
							self.updateCond(exp[2], dictLoc))
			elif len(exp) == 2 and exp[0] == EOpr['not'] :
				return Exp(EOpr['not'],(self.updateCond(exp[1], dictLoc)))
		return exp


	def additionalRead(self, p):
		if isinstance(p, Assertion):
			locVar = self.getLocations(p.cond)
			locVar = set(locVar)
			dictLoc = {}

			for v in locVar:
				dictLoc[v] = TempReg('val_'+str(v.address if isinstance(v, Location) else v))
			# print self.updateCond(p, dictLoc)
			return [ dictLoc[v] << v for v in locVar] + [Assertion(self.updateCond(p.cond, dictLoc))]
		elif isinstance(p, Assume):
			locVar = self.getLocations(p.cond)
			locVar = set(locVar)
			dictLoc = {}
			for v in locVar:
				dictLoc[v] = TempReg('val_'+str(v.address if isinstance(v, Location) else v))
			# print self.updateCond(p, dictLoc)
			return [ dictLoc[v] << v for v in locVar] + [Assume(self.updateCond(p.cond, dictLoc))]
		elif isinstance(p, ParallelSem):
			newPar = []
			for i in p.list():
				newPar += self.additionalRead(i)

			return [ParallelSem(*newPar)]
		elif isinstance(p, IfStm):
			newIf = []
			for i in p.list():
				newIf += self.additionalRead(i)
			return [IfStm(p.cond, *newIf)]
		elif isinstance(p, SeqSem):
			newSeq = []
			for i in p.list():
				newSeq += self.additionalRead(i)
			# print SeqSem(*newSeq)
			return [p.__class__(*newSeq)]
		else:
			return [p]

	def ssa(self):
		# eliminate havoc annotation
		# P = self.p
		[P] = self.eliminateHavoc(self.p)

		# realize reads for assertion and assumption
		[P] = self.additionalRead(P)

		return self.__ssa(P)


if __name__ == "__main__":
	P1 = SeqSem(
		InstrSem(	# mov r1, #1
			TempReg('val') << 1, 
			Register('r1') << TempReg('val')
			),
		IfStm( Register('z') == 0,
			InstrSem(	# str r1, [x]
				TempReg('val') << Register('r1'),
				ParallelSem(TempReg('val1') << Register('val'), TempReg('val2') << Register('val')),
				Location('x') << TempReg('val')
			)
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
	print P1
	P1 = invExtractor(P1, [Register('r2')])
	# P2 = invExtractor(P2, [Register('r2'), Register('r3'), Register('z'), Register('n'), Location('x'), Location('y')])
	for i in P1:
	# 	print i
		print '----- ssa -----'
		ssa_i = SSASem(i)
		j = ssa_i.ssa()
		print j
	

