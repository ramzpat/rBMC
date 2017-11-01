


from HWModel.OperatorSem import *
from Arch.arch_object import *
from z3 import *

class encodingFW:
	def __init__(self, model):
		if not model in self.supportedModels():
			raise KeyError('There are no such model')
		self.model = model


	def supportedModels(self):
		return []

	def new_write(self, var, exp, pid):
		raise NotImplementedError()
		return None 
	def new_read(self, var, exp, pid):
		raise NotImplementedError()
		return None
	def new_loc(self, addr):
		raise NotImplementedError()
		return None
	def new_branch(self, pid):
		raise NotImplementedError()
		return None
	def encodeOpr(self, i, info):
		raise NotImplementedError()
		return (None, info) 
	def encodeElement(self, e, info):
		raise NotImplementedError()
		return (True, info)

	def encodeSpecific(self):
		raise NotImplementedError()
		return True
	def getEvent(self, op):
		raise NotImplementedError()
		return None

	def encodeExp(self, exp):
		if isinstance(exp, int) or isinstance(exp, bool):
			return exp
		elif isinstance(exp, Register):
			raise NotImplementedError()
			return self.encodeElement(exp)
			# return herd.Const(str(exp), herd.Val)
		elif isinstance(exp, Exp):
			if(len(exp) > 2):
				op = exp[1]
				e1 = self.encodeElement(exp[0])
				e2 = self.encodeElement(exp[2])

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
					return And(e1, e2)
				elif op == EOpr['or']:
					return Or(e1, e2)
			elif len(exp) == 2:
				if exp[0] == EOpr['not']:
					e1 = self.encodeElement(exp[1])
					return Not(e1)
			else:
				e = self.encodeElement(exp[0])
				return e

	def program_order(self, PoSet = []):

		# http://stackoverflow.com/questions/8673482/transitive-closure-python-tuples
		# transitive-closure-python-tuples
		def transitive_closure(a):
			closure = set(a)
			while True:
				new_relations = set((x,w) for x,y in closure for q,w in closure if q == y)

				closure_until_now = closure | new_relations

				if closure_until_now == closure:
					break

				closure = closure_until_now
			return closure

		Ev = self.info['Ev']
		
		# for (i,j) in PoSet:
		# 	s.add(po(i, j)) 
		newPo = []
		EvID = [0 for i in range(0, self.info['EventCnt'])]
		for (i,j) in PoSet:
			newPo += [(i.eid, j.eid)]
			EvID[i.eid] = i
			EvID[j.eid] = j
		newPo = transitive_closure(newPo)

		# for x in Ev:
		# 	for y in Ev:
		# 		s.add(po(x,y) if (x.eid,y.eid) in newPo else Not(po(x,y)) )
		return newPo

	def encode(self, P, init_cond = [], init_locations = {}):
		# The set of events
		Ev = []

		self.info = {
			'CS':[],	# behaviors
			'PS':[],	# properties
			'Ev':[],	# events
			'iico':[],	# intra-instruction casual order
			'Pid':0,	# current process id

			'EventCnt':0,	# no. of events
			'RegCnt':0,		# no. of registers
			'Reg':{},		# set of registers
			'Loc':{},		# set of locations
			'Aux':{},
			'AuxCnt':0,

			# pairs of atomic (rmw)
			'RMW':[]
		}
		self.info['init_locations'] = init_locations

		# collect po, iico, Events(R,W,regRW)
		# locations, facts assignment
		# properties

		# change p to be operation in z3 wrt to structure...
		PoS = []
		self.info['Pid'] = 1
		for p in P:
			(poS, e) = self.constructPO(p, [])
			PoS += poS
			self.info['Pid'] += 1

		if len(self.info['Ev']) > 1:
			self.info['CS'] += [Distinct([ self.getEvent(e) for e in self.info['Ev'] if self.getEvent(e) != None ])]
			# print 'hey'
		if len(self.info['Loc']) > 1:
			self.info['CS'] += [Distinct(self.info['Loc'].values())]
		
		poS = self.program_order(PoS)
		self.info['poS'] = poS
		# print [str(v)for v in self.info['Loc'].values()]

		# initial location = 0 ?
		# if(init_location):
		# 	WriteInit = [self.new_write(v, 0, 0) for v in self.info['Loc'].values()]
		# 	self.info['Ev'] += WriteInit
		# else:
		# 	WriteInit = [self.new_write(v, FreshInt(), 0) for v in self.info['Loc'].values()]
		# 	self.info['Ev'] += WriteInit
		
		return self.encodeSpecific()

	def constructPO(self, p, prev = []):
		if isinstance(p, Assertion):
			ps = self.encodeElement(p.cond)
			self.info['PS'] += [ps]
			return ([], prev)
		elif isinstance(p, Assume):
			cs = self.encodeElement(p.cond)
			self.info['CS'] += [cs]
			return ([], prev)
		elif isinstance(p, LabelStm):
			return ([], prev)

		elif isinstance(p, Atomic):
			opr = p.opr 
			encodeOp = self.encodeOpr(opr)

			if isinstance(opr, ReadAssn):
				self.prevRead = encodeOp 
			elif isinstance(opr, WriteAssn):
				self.info['RMW'] += [(self.prevRead, encodeOp)]
			else:
				assert(False)

			# prepare program order 
			ret = []
			if encodeOp:
				for i in prev:
					ret += [(i, encodeOp)]

			# prepare a set of operations
			if encodeOp:
				self.info['Ev'] += [encodeOp]	

			retE = [encodeOp] if encodeOp else prev
			return (ret, retE)

		elif isinstance(p, Operation):
			# encode each operation... 
			encodeOp = self.encodeOpr(p)

			# prepare program order 
			ret = []
			if encodeOp:
				for i in prev:
					ret += [(i, encodeOp)]

			# prepare a set of operations
			if encodeOp:
				self.info['Ev'] += [encodeOp]	

			retE = [encodeOp] if encodeOp else prev
			return (ret, retE)
		# elif isinstance(p, RmwStm):
		# 	# 1-get all operations that should be atomic 
		# 	poRet = []
		# 	for pl in p.list():
		# 		(po,e,info) = constructPO(pl, prev, info)
		# 		poRet += po
		# 		prev = e 
		# 	r = po[0][0]
		# 	w = po[0][1]
			
		# 	# 2-add constraints for those operations (no another processor can interrupt)
		# 	info['RMW'] += [(r,w)]
		# 	return (poRet, prev, info)

		elif isinstance(p, ParOps):
			poRet = []
			lastEle = []
			for pl in p.elements:
				(po, e) = self.constructPO(pl, prev)
				lastEle += e 
				poRet += po
			return (poRet, lastEle if lastEle != [] else prev)
		elif isinstance(p, InstrOps):
			poRet = []
			iico = []
			# print prev
			prev2 = []
			for pl in p.elements:
				(po, e) = self.constructPO(pl, prev2)
				poRet += po
				prev2 = e if e != [] else prev2

			self.info['iico'] += poRet
			# print prev, poRet[0][0]
			# try:
			
			if len(poRet) > 0:
				poRet = [ (pl, poRet[0][0]) for pl in prev] + poRet
			elif prev2 != []:
				poRet += [(pl, pl2) for pl in prev for pl2 in prev2]

			# except IndexError:
			# 	print 'Bug', prev, poRet, p
			# print prev2, 'pr2', p
			return (poRet, prev2 if prev2 != [] else prev)
		elif isinstance(p, SeqOps):
			poRet = []
			for pl in p.elements:
				(po, e) = self.constructPO(pl, prev)
				
				poRet += po
				if e != []:
					prev = e 
			return (poRet, prev)
		# print p
		assert(False)

