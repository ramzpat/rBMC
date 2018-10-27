if __package__ is None:
	import sys
	from os import path
	sys.path.append( (path.dirname( path.dirname( path.abspath(__file__) ) ) ))
# 	from Encoder.GenericEncode import *
# 	from Ops.objects import *
# else:
from GenericEncode import *
from Ops.objects import *

from Framework.gharachorloo import encoder  as gFW 
from Framework.herdingCats import encoder as hFW 


frameworks_list = {	'gharachorloo': gFW, 
					'herding_cats': hFW,
					}

def isVar(i):
	return isinstance(i, Register) or isinstance(i, AuxVar)

def ssa_form(P):
	if not isinstance(P, list):
		P = [P]

	def new_var(set_name, state):
		# state['dynamic_nickname']
		# state['dynamic_vars']
		# state['dynamic_cnt']

		if(set_name in state['dynamic_vars']):
			var_name = state['dynamic_nickname'][set_name]+'_'+str(state['pid'])+'_'+str(state['dynamic_cnt'][set_name])
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
			var_name = state['dynamic_nickname'][set_name]+'_'+str(state['pid'])+'_'+str(state['dynamic_cnt'][set_name]-1)
			return var_name
		elif (set_name in state['write_val']):
			# print 'heyhey', state['write_val'][set_name.address]
			return state['write_val'][set_name]
		else:
			return 'undefined'	
			raise NameError('There are no variable name "' + set_name + '"')
			name, state = new_var(set_name, state)
			return  name # wrong

	def new_exp(exp, state):
		if isinstance(exp, Location):
			return Exp(state['write_val'][exp.address])
		elif isVar(exp):
			# print exp, exp.__class__
			clss = exp.__class__ 
			# print str(exp), clss
			name = get_last_var(str(exp), state)
			if name == 'undefined':
				return undefinedExp()
			return Exp( clss(name) )
		elif isinstance(exp, ifExp):
			return ifExp( new_exp(exp.cond, state), 
							 new_exp(exp.t_exp, state),
							 new_exp(exp.f_exp, state) )
		elif isinstance(exp, Exp):
			if len(exp) > 2:
				ep1 = new_exp(exp[0], state)
				ep2 = new_exp(exp[2], state)
				if (isinstance(ep1, undefinedExp) or isinstance(ep2, undefinedExp)):
					if (exp[1] == EOpr['plus'] or exp[1] == EOpr['minus'] or exp[1] == EOpr['times'] or 
						exp[1] == EOpr['divide']):
						return undefinedExp()
					elif (exp[1] == EOpr['eq'] or exp[1] == EOpr['lt'] or exp[1] == EOpr['gt'] or 
						  exp[1] == EOpr['or']):
						return True
					elif (exp[1] == EOpr['and'] and not isinstance(ep1, undefinedExp)):
						return ep1 
					elif (exp[1] == EOpr['and'] and not isinstance(ep2, undefinedExp)):
						return ep2 
					elif (exp[1] == EOpr['and'] and isinstance(ep1, undefinedExp) and isinstance(ep2, undefinedExp)):
						return True
				elif (exp[1] == EOpr['plus'] or exp[1] == EOpr['minus'] or exp[1] == EOpr['times'] or 
					exp[1] == EOpr['divide'] or exp[1] == EOpr['eq'] or exp[1] == EOpr['lt'] or exp[1] == EOpr['gt'] or
					exp[1] == EOpr['and'] or exp[1] == EOpr['or']  ):
					return Exp( new_exp(exp[0], state),
								exp[1],
								new_exp(exp[2], state))
				else:
					assert(False)
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
			if isinstance(e, Atomic):
				state = newOpr(e.opr, state)
		elif isinstance(e, Operation):
			if isinstance(e, Assignment):
				var = e.var
				exp = e.exp 
				var_name = str(var.name) if (isinstance(var, AuxVar)) else str(var)
				nExp = (exp if (isinstance(exp, Location) or isinstance(exp, AuxVar)) else new_exp(exp, state))
				if isinstance(var, AuxVar):
					(nVar, state) = (var_name, state)
				else:
					(nVar,state) = (var.address,state) if (isinstance(var, Location)) else new_var(var_name, state)
				# save write value state 
				if isinstance(var, Location):
					state['write_val'][var.address] = nExp
				e.var = var.__class__(nVar)
				e.exp = nExp 
			elif isinstance(e, fenceStm):
				pass 
			elif isinstance(e, branchOp):
				pass
			# elif isinstance(e, Reserve):
			# 	assert(False)
			# 	pass
			elif isinstance(e, OprLoadLink):
				var = e.var
				var_name = str(var)
				(nVar, state) = new_var(var_name, state)
				e.var = var.__class__(nVar)
			elif isinstance(e, OprStoreCond):
				var = e.var 
				exp = e.exp 
				nExp = new_exp(exp, state)
				(nVar, state) = new_var(str(var), state)

				# save write value state 
				state['write_val'][e.loc.address] = nExp

				e.var = var.__class__(nVar)
				e.exp = nExp 
			elif isinstance(e, Operation):
				pass 
			else:
				print e
				assert(False)
		elif isinstance(e, Ops):
			# if isinstance(e, InstrOps):

			for i in e.elements:
				state = newOpr(i, state)

		return state 


	# [P] = self.additionalRead(P)
	def getLocations(exp):
		if isinstance(exp, Location):
			return []
			# return [exp]
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
			return exp
			# return (dictLoc[exp.address] if (str(exp.address) in dictLoc.keys()) else exp)
		elif isinstance(exp, TempReg):
			return exp
		elif isinstance(exp, Register):
			return (dictLoc[exp] if (str(exp) in dictLoc.keys()) else exp)
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

	def lastestWriteVal(p, dictLoc = {}):
		if isinstance(p, Assertion):
			print updateCond(p.cond, dictLoc)
			return (SeqOps(Assertion(updateCond(p.cond, dictLoc))), dictLoc)
		elif isinstance(p, Assume):
			print updateCond(p.cond, dictLoc), dictLoc
			return (SeqOps(Assume(updateCond(p.cond, dictLoc))), dictLoc)
		elif isinstance(p, WriteAssn) and isinstance(p.var, Location):
			print 'save ', p.var.address, p.exp
			dictLoc[p.var.address] = p.exp
			return (p, dictLoc)
		elif isinstance(p, OprStoreCond):
			print 'save ', p.loc.address, p.exp
			dictLoc[p.loc.address] = p.exp
			return (p, dictLoc)
		elif isinstance(p, Operation):
			return (p,dictLoc) 
		elif isinstance(p, SeqOps):
			new_elements = SeqOps()
			for i in p.elements:
				(nP, dictLoc) = lastestWriteVal(i, dictLoc)
				new_elements.append(nP)
			return (new_elements, dictLoc)

		elif isinstance(p, ParOps):
			new_elements = ParOps()
			for i in p.elements:
				(nP, dictLoc) = lastestWriteVal(i, dictLoc)
				new_elements.append(nP)
			return (new_elements, dictLoc)
		elif isinstance(p, InstrOps):
			new_elements = InstrOps()
			for i in p.elements:
				(nP, dictLoc) = lastestWriteVal(i, dictLoc)
				new_elements.append(nP)
			return (new_elements, dictLoc)
		elif isinstance(p, AnnotatedStatement):
			return (p,dictLoc)
		elif isinstance(p, Ops):
			return (p,dictLoc)
		elif isinstance(p, fenceStm):
			return (p,dictLoc)
		print p.__class__
		assert(False)

	def additionalRead(p):
		if isinstance(p, Assertion):
			locVar = getLocations(p.cond)
			locVar = set(locVar)
			dictLoc = {}

			for v in locVar:
				if not isinstance(v, Location):
					dictLoc[v] = TempReg('val_'+str(v.address if isinstance(v, Location) else v))
			# print self.updateCond(p, dictLoc)
			return SeqOps( *([dictLoc[v] << v for v in locVar if not isinstance(v,Location)] + [Assertion(updateCond(p.cond, dictLoc))]) )
		elif isinstance(p, Assume):
			locVar = getLocations(p.cond)
			locVar = set(locVar)
			dictLoc = {}
			for v in locVar:
				if not isinstance(v, Location):
					dictLoc[v] = TempReg('val_'+str(v.address if isinstance(v, Location) else v))
			# print self.updateCond(p, dictLoc)
			return SeqOps( *([ dictLoc[v] << v for v in locVar if not isinstance(v,Location)] + [Assume(updateCond(p.cond, dictLoc))]))

		elif isinstance(p, Assignment) and isinstance(p.exp, ifExp):
			locVar = getLocations(p.exp.cond)
			locVar = set(locVar)
			dictLoc = {}

			for v in locVar:
				dictLoc[v] = TempReg('val_'+str(v.address if isinstance(v, Location) else v))

			return SeqOps( *( [ dictLoc[v] << v for v in locVar if not isinstance(v,Location)] + [p.var << ifExp( updateCond(p.exp.cond, dictLoc), p.exp.t_exp, p.exp.f_exp )]) )

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
		elif isinstance(p, fenceStm):
			return p
		print p.__class__
		assert(False)

	def eliminateHavoc(p):
		if isinstance(p, havoc):
			return [ v << undefinedExp() for v in p.vars]
		elif isinstance(p, havocW):
			return [TempReg('val_'+str(p.loc.address)) << undefinedExp() , 
			    	p.loc << TempReg('val_'+str(p.loc.address))] 
		elif isinstance(p, ParOps):
			newPar = []
			for i in p.elements:
				newPar += eliminateHavoc(i)

			return [ParOps(*newPar)]
		# elif isinstance(p, IfStm):
		# 	newSeq = []
		# 	for i in p.list():
		# 		newSeq += self.eliminateHavoc(i)
		# 	# print SeqSem(*newSeq)
		# 	return [IfStm(p.cond, *newSeq)]
		elif isinstance(p, Ops):
			newSeq = []
			for i in p.elements:
				newSeq += eliminateHavoc(i)
			# print SeqSem(*newSeq)
			# print p.__class__
			return [p.__class__(*newSeq)]
		else:
			return [p]

	def ssa_seq(P, state = {}):
		# print SeqOps, ' vs ', P.__class__
		assert(isinstance(P, SeqOps))

		[P] = eliminateHavoc(P)
		# extract loop first!
		

		P = P.clone()
		# (P, dictLoc) = lastestWriteVal(P)
		P = additionalRead(P)
		# print P 
		for i in P.elements:
			state = newOpr(i, state)
		# print P
		return (P, state)

	state = {
		'pid' : 0,
		'dynamic_nickname' : {},
		'dynamic_vars' : {},
		'dynamic_cnt' : {},
		'write_val' :{}
	}
	ssa = []
	pid = 0
	for p in P:	
		state['pid'] = pid
		# if 'lock' in state['write_val'].keys():
		# 	print state['write_val']['lock']

		state['dynamic_nickname'] = {}
		state['dynamic_vars'] = {}
		state['dynamic_cnt'] = {}

		state['write_val'] = {}

		(e, state) = ssa_seq(p, state)
		ssa += [e]
		pid += 1
	return ssa 

# return z3 formulas 
def encode(P, encoder, model = ''):
	if encoder in frameworks_list.keys():
		encoder = frameworks_list[encoder](model)

	# print encoder.__class__, ' vs ', encodingFW
	if isinstance(encoder, encodingFW):
		P = ssa_form(P)
		# return None
		formulas = encoder.encode(P)
		return formulas
	assert(False)

# encode([], 'gharachorloo','TSO')