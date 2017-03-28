
from Arch.arch_object import *


def isVar(i):
	return isinstance(i, Register)

def newExp(exp, lastVarName):
	if isVar(exp):
		clss = exp.__class__ 
		return Exp( clss(lastVarName(str(exp))) )
	elif isinstance(exp, i_if_exp):
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


