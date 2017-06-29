# SMT encoder


from HWModel.OperatorSem import *
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
			clss = exp.__class__ 
			return Exp( clss(get_last_var(str(exp), state)) )
		elif isinstance(exp, i_if_exp):
			return i_if_exp( new_exp(exp.cond, state), 
							 new_exp(exp.t_exp, state),
							 new_exp(exp.f_exp, state) )
		elif isinstance(exp, Exp):
			if len(exp) > 2 and (exp[1] == EOpr['plus'] or exp[1] == EOpr['minus'] or exp[1] == EOpr['times'] or 
				exp[1] == EOpr['divide'] or exp[1] == EOpr['eq'] or exp[1] == EOpr['lt'] or exp[1] == EOpr['gt'] or
				exp[1] == EOpr['and'] or exp[1] == EOpr['or']  ):
				return Exp( new_exp(exp[0], state),
							exp[1],
							newExp(exp[2], state))
			elif len(exp) == 2 and exp[0] == EOpr['not'] :
				return Exp(EOpr['not'],(newExp(exp[1], state)))
			# else:
			# 	return newExp(exp[0], lastVarName)
		return exp

	def newOpr(e, state):
		assert(isinstance(e, Operation) or isinstance(e, Ops) or isinstance(e, AnnotatedStatement))
		if isinstance(e, AnnotatedStatement):
			return state
		elif isinstance(e, Operation):
			if isinstance(e, Assignment):
				var = e.var
				exp = e.exp 
				var_name = str(var)
				nExp = exp if (isinstance(var, Location)) else new_exp(exp, state)
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

	def ssa_seq(P, state = {}):
		assert(isinstance(P, SeqOps))
		P = P.clone()
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



class encodingFW:
	pass