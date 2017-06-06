# HW_Model in z3 definition
# import z3
from hw_z3 import *
from abc import ABCMeta, abstractmethod

from encode_z3 import *

import itertools

# Utilities function
# Emulate w \in writes 
def restrict(w, writes = []):
	ret = [False]
	for (m,l,i) in writes:
		ret += [(w == m)]
	return Or(ret)

# check two operators are conflict 
def is_conflict(w1, w2):
	(wA, locA, pA) = w1
	(wB, locB, pB) = w2
	return (wA.sort() == WriteOp or wB.sort() == WriteOp) and (eq(locA,locB))		

# collect a list of conflicting writes wrt memory operation rw
def conflict_writes(writes, rw):
	ret = []
	for w in writes:
		if is_conflict(w, rw):
			ret += [w]
	return ret

# Hardware model for abstract memory consistency model
class HWModel(object):
	__metaclass__ = ABCMeta

	def axioms(self, info):
		# Basis behaviors under a general model
		# + X_M : constraints of memory model M
		return self.based_axioms(info)  + self.model_axioms(info)

	def initial_location(self, locations, value = 0):
		ax = []
		for l in locations:
			L = Const(str(l), Loc)
			ax += [initial_value(L) == value]
		return ax

	def additional_axioms(self, **info):
		loc = info['Loc']
		reads = info['MemOp']['read']
		writes = info['MemOp']['write']
		rmws = info['MemOp']['rmw']
		proc = info['Proc']

		xo_axioms = self.generate_xo(loc, writes, reads, proc, rmws)
		return_axioms = self.generate_return_value_cond2(loc, reads, writes, rmws, proc)
		# return_axioms = self.generate_return_value_cond(loc, reads, writes, rmws, proc)

		return xo_axioms + return_axioms

	@abstractmethod
	def model_axioms(self):
		pass 

	def unique_MemOp(self):
		m = Const('m', MemOp)
		return [ForAll([m], m == either())]

	# Axiom for model
	# Behavior property (basisS)
	def based_axioms(self, info):
		
		# Conflict 
		def conflict_def(w1, w2):
			(wA, locA, pA) = w1
			(wB, locB, pB) = w2
			if wA.sort() == WriteOp or wB.sort() == WriteOp:
				return (hw.conflict(wA, wB) == eq(locA,locB))
			else: 
				return (Not(hw.conflict(wA, wB)))

		conflict_manual_def = []
		write = info['MemOp']['write']
		read = info['MemOp']['read']
		rmwList = info['MemOp']['rmw']
		memOp = write + read
		# for (a, loc, p) in rmwList:
		# 	memOp += [(hw.atomic_write(a),loc,p), (hw.atomic_read(a), loc, p)]
		conflict_manual_def += [ conflict_def(w1, w2) for (w1, w2) in itertools.permutations(memOp, 2)]
		
		# -co-> definition
		def co_def(w1, w2):
			(wA, locA, pA) = w1
			(wB, locB, pB) = w2
			i = Const('i', Proc)
			if (wA.sort() == WriteOp or wB.sort() == WriteOp) and (locA == locB):
				return (hw.co(wA, wB) == Exists([i],xo(subOpr(wA,i), subOpr(wB,i))))
			else:
				return Not(hw.co(wA, wB))

		# -co'-> definition
		def ico_def(w1, w2):
			(wA, locA, pA) = w1
			(wB, locB, pB) = w2
			i = Const('i', Proc)
			if (wA.sort() == WriteOp or wB.sort() == WriteOp) and (locA == locB) and not eq(pA,pB):
				return (hw.ico(wA, wB) == Exists([i],xo(subOpr(wA,i), subOpr(wB,i))))
			else:
				return Not(hw.ico(wA, wB))

		conflict_manual_def += [ co_def(w1, w2) for (w1, w2) in itertools.permutations(memOp, 2)]
		conflict_manual_def += [ ico_def(w1, w2) for (w1, w2) in itertools.permutations(memOp, 2)]

		# print conflict_manual_def


		rw1, rw2 = Consts('rw1 rw2', MemOp)
		# rmw = Const('rmw', AtomicOp)
		# rmw1, rmw2 = Consts('rmw1 rmw2', AtomicOp)
		w = Const('w', WriteOp)
		r1, r2 = Consts('r1 r2', ReadOp)
		i, j = Consts('i j', Proc)
		
		def __atomicExce(subAtomR, subAtomW, subW):
		# return And( xo(subAtomR, subW), xo(subAtomW, subW) )
			return Xor( 
					And( xo(subAtomR, subW), xo(subAtomW, subW) ),
					And( xo(subW, subAtomR), xo(subW, subAtomW) ))

		# Cond 3 : read-modify-write behaviors
		axioms_atomic = []
		for ((rmw_r, loc, pi), (rmw_w, loc, pi)) in rmwList:
			axioms_atomic += [
				ForAll(w, 
						Implies(
							And(conflict(rmw_w, w)),
							__atomicExce(
								subOpr(rmw_r, pi), 
								subOpr(rmw_w, pi), 
								subOpr(w, pi)
								)
							)
					)
			]

		# Partial order axioms 
		def DeclareList(sort):
		    List = Datatype('List_of_%s' % sort.name())
		    List.declare('cons', ('car', sort), ('cdr', List))
		    List.declare('nil')
		    return List.create()

		def partial_order_axioms(func):	
			assert(func.domain(0) == func.domain(1))
			x, y, z  = Consts('x y z', func.domain(0))
			irreflexive_axiom = ForAll([x,y], Implies(func(x,y), x != y) )
			# asymetric_axiom = ForAll([x,y], Implies( func(x,y), Not( func(y,x) )))
			transitivity_axiom = ForAll([x,y,z], Implies( And(func(x,y), func(y,z)), func(x,z) ))
			return [
				irreflexive_axiom, 
				# asymetric_axiom, 
				transitivity_axiom
				]

		# asymetric for xo
		x, y = Consts('x y', SubOpr)
		a, b = Consts('a b', MemOp)
		i, j = Consts('i j', Proc)
		addition_order = [
			ForAll([x,y], Implies( xo(x,y), Not( xo(y,x) ))),
			ForAll([a,b], Implies(issue_proc(a) != issue_proc(b), Not(po(a,b)) )),
			ForAll([a,b], Implies(And(issue_proc(a) == issue_proc(b), po(a,b)), Not(po(b,a) )))
		]
		
		return (
			conflict_manual_def
			# + conflict_def_axiom
			# + inconflict_def_axiom 
			+ partial_order_axioms(po) 
			+ partial_order_axioms(xo)
			+ addition_order
			+ axioms_atomic 
			)


	# Additional conditions for programs behaviors
	# Condition 4.4 + 4.5
	def generate_xo(self, location, write = [], read = [], proc = [], rmw = []):
		# write += [(atomic_write(a),l,i) for (a,l,i) in rmw]
		# read += [(atomic_read(a),l,i) for (a,l,i) in rmw]
		
		listSubOprW = [subOpr(w, i) for i in proc for (w,l,j) in write ]
		listSubOprR = [subOpr(r, i) for (r,l,i) in read ]

		listAxioms = []
		listAxioms += [
				Xor(xo(x,y), xo(y,x)) 
			for (x,y) in itertools.combinations(listSubOprW, 2)]
		listAxioms += [
				Xor(xo(x,y), xo(y,x)) 
			for x in listSubOprW for y in listSubOprR]
		return listAxioms 

	WPO = Function('wpo', MemOp, MemOp, BoolSort())	
	WXO = Function('wxo', MemOp, MemOp, Proc, BoolSort())

	ConseqPO = Function('conseq_po', MemOp, MemOp, BoolSort())
	ConseqXO = Function('conseq_xo', MemOp, MemOp, BoolSort())

	ConseqPO.domain = (lambda i: MemOp)
	ConseqXO.domain = 	(lambda i: MemOp)

	WPO.domain = (lambda i: MemOp)
	WXO.domain = (lambda i: MemOp if i < 2 else Proc )


	# Condition 4.6(E.1) : Return value for read sub-operations
	def generate_return_value_cond2(self, location, read = [], write = [], rmw = [], proc = []):
		

		def no_write_cond(r, i, cond, writes = []):
			w = Const('w', WriteOp)
			return [
			(	ForAll([w], 
					Implies(
						And(restrict(w, writes),	# w in Ws(conflict with r)
							conflict(r, w), 			# conflict(r, w)
							po(w,r)),					# w -po-> r
						(xo(subOpr(w,i), subOpr(r,i)))	# implies w(i) -xo-> r(i)
					)
				)
			),(	ForAll([w],
					Implies(
						And(
							restrict(w, writes),	# w in Ws(conflict with r)
							conflict(r,w)),				# conflict(r, w)
						(xo(subOpr(r,i), subOpr(w,i)))	# implies r(i) -xo-> w(i)
					)
				)
			)
			][cond]

		def consecutive_write(r, w, i, cond ):
			return  [
			(	And( 
					conflict(r,w), po(w,r),
					xo(subOpr(r,i), subOpr(w,i)), 
					(self.WPO(w,r))
				)
			),
			(
				And(
					conflict(r,w),
					xo(subOpr(w,i), subOpr(r,i)), 
					(self.WXO(w,r,i))
				)		
			)
			][cond]

		def genWPOCond(w, r, listW = []):
			# listW.remove(w)
			ret = [And(po(w,r), conflict(w,r))]
			for (wj,l,i) in listW:
				if(not eq(w,wj)):
					ret += [Xor( And( po(wj, w), po(wj, r) ), 
										And( po(w, wj), po(r, wj)))]
			return And(ret)

		def genWXOCond(w,r, i,listW = []):
			# listW.remove(w)
			subOprW = subOpr(w,i)
			subOprR = subOpr(r,i)	
			ret = xo(subOprW, subOprR)
			for (wj,l,i) in listW:
				if(not eq(w,wj)):
					subOprWj= subOpr(wj,i)
					ret = And( ret, Xor( And(xo(subOprWj, subOprR), xo(subOprWj, subOprW) ),
										 And(xo(subOprR, subOprWj), xo(subOprW, subOprWj) ) ) )
			return ret

		

		# ---------- Process 
		# write += [ (atomic_write(a),l,k) for (a,l,k) in rmw ]
		# read += [ (atomic_read(a),l,k) for (a,l,k) in rmw ]
	
		wj = Const('wj', WriteOp)
		i,j = Consts('i j', Proc)

		return_axioms = []
		for (y, l, k) in read:
			writes_conflict_r = conflict_writes(write, (y,l,k))
			return_axioms += [
				If( And(no_write_cond(y,k,0, writes_conflict_r), no_write_cond(y,k,1, writes_conflict_r)), 
						# return_val(y) == initial_value(mem_access(y)) 
						return_val(y) == 0
						,If(no_write_cond(y,k,0, writes_conflict_r), 
							Exists([wj], 
								And(restrict(wj,writes_conflict_r),		# w in Ws(conflict r)
									conflict(wj, y),							# confirm conflict again
									xo(subOpr(wj, k), subOpr(y, k)),			# wj(i) -xo-> r(i)
									self.ConseqXO(wj, y),
									# consecutive_write(y,wj,k,1), 				
									(return_val(y) == write_val(wj)) )), 
						Exists([wj], 
							And(restrict(wj,writes_conflict_r),			# w in Ws(conflict r)
								conflict(wj, y),								# confirm conflict again
								xo( subOpr(y,k), subOpr(wj, k) ),				# r(i) -xo-> wj(i)
								self.ConseqPO(wj, y), 			
								(return_val(y)) == write_val(wj)))
					)
				)
			]
		conseq_po = []
		conseq_xo = []
		for (r, locA, i) in read:
			writes_conflict_r = conflict_writes(write, (r, locA, i))
			for (w, locB, j) in writes_conflict_r:
				retPo = [po(w,r)] 	# w -po-> r
				retXo = [True]
				subOprW = subOpr(w,i)
				subOprR = subOpr(r,i)	
				for (wj,l,k) in writes_conflict_r:
					if(not eq(w,wj)):
						subOprWj = subOpr(wj, i)
						retPo += [Xor( And( po(wj, w), po(wj, r) ), 
											And( po(w, wj), po(r, wj)))]
						retXo += [Xor( And(xo(subOprWj, subOprR), xo(subOprWj, subOprW) ),
										 And(xo(subOprR, subOprWj), xo(subOprW, subOprWj) ) )]
				conseq_po += [self.ConseqPO(w,r) == And(retPo)]
				conseq_xo += [self.ConseqXO(w,r) == And(retXo)]
			
		# print conseq_po
		return return_axioms + conseq_po + conseq_xo

	def generate_return_value_cond(self, location, read = [], write = [], rmw = [], proc = []):
		
		def restrict(w, writes = []):
			ret = [False]
			for (m,l,i) in writes:
				ret += [(w == m)]
			return Or(ret)

		def no_write_cond(r, i, cond):
			w = Const('w', WriteOp)
			return [
			(	ForAll([w], 
					Implies(
						And(conflict(r, w), po(w,r)),
						(xo(subOpr(w,i), subOpr(r,i)))
					)
				)
			),(	ForAll([w],
					Implies(
						And(conflict(r,w)),
						(xo(subOpr(r,i), subOpr(w,i)))
					)
				)
			)
			][cond]

		def genWPOCond(w, r, listW = []):
			# listW.remove(w)
			ret = [And(po(w,r), conflict(w,r))]
			
			for (wj,l,i) in listW:
				if(not eq(w,wj)):
					ret += [Xor( And( po(wj, w), po(wj, r) ), 
										And( po(w, wj), po(r, wj)))]
			return And(ret)

		def genWXOCond(w,r, i,listW = []):
			# listW.remove(w)
			subOprW = subOpr(w,i)
			subOprR = subOpr(r,i)	
			ret = xo(subOprW, subOprR)
			for (wj,l,i) in listW:
				if(not eq(w,wj)):
					subOprWj= subOpr(wj,i)
					ret = And( ret, Xor( And(xo(subOprWj, subOprR), xo(subOprWj, subOprW) ),
										 And(xo(subOprR, subOprWj), xo(subOprW, subOprWj) ) ) )
			return ret

		def consecutive_write(r, w, i, cond ):
			return  [
			(	And( 
					conflict(r,w), po(w,r),
					xo(subOpr(r,i), subOpr(w,i)), 
					(self.WPO(w,r))
				)
			),
			(
				And(
					conflict(r,w),
					xo(subOpr(w,i), subOpr(r,i)), 
					(self.WXO(w,r,i))
				)		
			)
			][cond]
		w = Const('w', WriteOp)
		wj = Const('wj', WriteOp)
		r = Const('r', ReadOp)

		# write += [ (atomic_write(a),l,k) for (a,l,k) in rmw ]
		# read += [ (atomic_read(a),l,k) for (a,l,k) in rmw ]
	
		i,j = Consts('i j', Proc)

		# ----- WPO
		wpo_axioms = [self.WPO(x,y) == genWPOCond(x, y, write[:]) for (x,l2,j) in write for (y,l,k) in read]
		wpo_axioms += [
			ForAll([w,r],  #else cases
				Implies(
					Or(
						Not(conflict(w,r),
						po(r,w)
						)
					),
					Not(self.WPO(w,r))
				)
			),
		]

		# ------- WXO
		# generate wxo ?
		wxo_axioms = [self.WXO(x,y,k) == genWXOCond(x,y,k,write[:]) for (x,l2,j) in write for (y,l,k) in read]
		 # Else wxo
		for k in proc:
			wxo_axioms += [
				ForAll([w,r], 
					Implies(Not(conflict(w,r)),
						Not(self.WXO(w,r,k))
					)
				)
			]
		
		return_axioms = [
				If( And(no_write_cond(y,k,0), no_write_cond(y,k,1)), 
						# return_val(y) == initial_value(mem_access(y)) 
						return_val(y) == 0
						,If(no_write_cond(y,k,0), Exists([wj], And(restrict(wj,write),consecutive_write(y,wj,k,1), 
							(return_val(y)) == write_val(wj))), 
						Exists([wj], And(restrict(wj,write),consecutive_write(y,wj,k,0), (return_val(y)) == write_val(wj)))
					)
				)
				for (y,l,k) in read
			]

		return_axioms += [
				ForAll([wj], 
					Implies(
						Not(restrict(wj,write)) , 
						Not(consecutive_write(y, wj, k, 0))
					) 
				)
				for (y,l,k) in read
			]
		return_axioms += [
				ForAll([wj], 
					Implies(
						Not(restrict(wj,write)) , 
							Not(consecutive_write(y, wj, k, 1))
					) 
				)
				for (y,l,k) in read
			]
		return (
				return_axioms
				+ wpo_axioms
				+ wxo_axioms
				) 

	def genAtomicFacts(rmw):
		return [
			# consists of read and write
			po(atomic_read(rmw), atomic_write(rmw)),
			# atomic-read
			issue_proc(atomic_read(rmw)) == issue_proc(rmw),
			# mem_access(atomic_read(rmw)) == mem_access(rmw),
			# ret_val(atomic_read(rmw)) == return_val(rmw),
			# atomic-write
			issue_proc(atomic_write(rmw)) == issue_proc(rmw),
			# mem_access(atomicWrite(rmw)) == mem_access(rmw),
			# write_val(atomicWrite(rmw)) == write_val(rmw),
		]

	