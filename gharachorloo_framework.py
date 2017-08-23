# Gharachorloo framework



from encodingFW import *


# Abstract model def 
Proc = 		DeclareSort('Proc') 			# Processor
Loc = 		DeclareSort('Loc')				# Location
Opr = 		DeclareSort('Opr')				# Operation
Val = 		IntSort()						# Value in the systems

MemOp = 	DeclareSort('MemOp')			# Memory operation 	
# AtomicOp =	DeclareSort('AtomicOp')			# Atomic operation 	
FenceOp =	DeclareSort('FenceOp')			# Fence operation 	

# Additional Op
MembarWR =	DeclareSort('MEMBAR(WR)')				# MEMBER(WR) operation in TSO+ (spac v8+) 
STBar = DeclareSort('STBar')
membarOp = Function('f_membar', MembarWR, FenceOp)	# a wrapper function
stbarOp = Function('f_stbar', STBar, FenceOp)	# a wrapper function
FenceOp.cast = (lambda val:
	val if (val.sort() == FenceOp)
	else stbarOp(val) if (val.sort() == STBar)
	else membarOp(val)
)

ReadOp = 	DeclareSort('ReadOp')			# Read access 	*A kind of memory operation(MemOp)
WriteOp = 	DeclareSort('WriteOp')			# Write access 	*A kind of memory operation(MemOp) 

SubOpr =	DeclareSort('SubOpr')			# Memory access on a specific Processor 	*generated by memory operation(MemOp)

# Functions 
# Wrapper functions
memOp =		Function('memOp', MemOp, Opr)			# MemOp is a subsort of Instr
# atomicOp =	Function('atomicOp', AtomicOp, Opr) 	# AtomicOp is a subsort of Instr
fenceOp =	Function('fenceOp', FenceOp, Opr)		# fenceOp is a subsort of Instr
read = 		Function('read', ReadOp, MemOp)			# ReadOp is a subsort of MemOp
write = 	Function('write', WriteOp, MemOp)		# WriteOp is a subsort of MemOp
subOpr = 	Function('subOpr', MemOp, Proc, SubOpr)	# A constructor for SubOpr

# Program define function
issue_proc =	Function('issue_proc', Opr, Proc)
mem_access = 	Function('mem_access', MemOp, Loc)
write_val =		Function('write_val', WriteOp, Val)
return_val = 	Function('return_val', ReadOp, Val)

initial_value = Function('initial_value', Loc, Val)
final_value = Function('final_value', Loc, Val)

# Predicates 
conflict = 		Function('conflict', MemOp, MemOp, BoolSort())		# Conflict 
po =			Function('po', Opr, Opr, BoolSort())				# Program order (Opr)
xo = 			Function('xo', SubOpr, SubOpr, BoolSort())			# Execution order 
co = 			Function('co', MemOp, MemOp, BoolSort())			# Conflict order 
ico = 			Function('ico', MemOp, MemOp, BoolSort())			# Inter conflict order 

# Value casting
Opr.cast = (lambda val:
		val if (val.sort() == Opr)
		# else atomicOp(val) if ( val.sort() == AtomicOp )
		else fenceOp(val) if ( val.sort() == FenceOp )
		else memOp(MemOp.cast(val)) if ( val.sort() == MemOp or val.sort() ==  ReadOp or val.sort() == WriteOp )
		else fenceOp(FenceOp.cast(val))
	)
MemOp.cast = (lambda val:
		val if (val.sort() == MemOp)
		else read(val) if (val.sort() == ReadOp)
		else write(val) 
	)

subOpr.domain = (lambda i: MemOp if i == 0 else Proc)

issue_proc.domain = (lambda i: Opr)
mem_access.domain = (lambda i: MemOp)
write_val.domain = (lambda i: WriteOp)
return_val.domain = (lambda i: ReadOp)

conflict.domain = (lambda i: MemOp)
po.domain = (lambda i: Opr)
xo.domain = (lambda i: SubOpr)
co.domain = (lambda i: MemOp)
ico.domain = (lambda i: MemOp)

WPO = Function('wpo', MemOp, MemOp, BoolSort())	
WXO = Function('wxo', MemOp, MemOp, Proc, BoolSort())

ConseqPO = Function('conseq_po', MemOp, MemOp, BoolSort())
ConseqXO = Function('conseq_xo', MemOp, MemOp, BoolSort())

ConseqPO.domain = (lambda i: MemOp)
ConseqXO.domain = 	(lambda i: MemOp)

WPO.domain = (lambda i: MemOp)
WXO.domain = (lambda i: MemOp if i < 2 else Proc )



def enum(*sequential, **named):
    enums = dict(zip(sequential, range(len(sequential))), **named)
    return type('Enum', (), enums)

FenceType = enum('STBar', 'MEMBAR_WR')


# additional fence
class STBarFence(fenceStm):
	def __str__(self):
		return 'stbar()' 

class MEM_WR_Fence(fenceStm):
	def __str__(self):
		return 'MEMBAR(WR)'

# Utilities function
# Emulate w \in writes 
def restrict(w, writes = []):
	ret = [False]
	for m in writes:
		ret += [(w == m)]
	return Or(ret)

def is_RW(rw):
	return rw.sort() == WriteOp or rw.sort() == ReadOp or rw.sort() == MemOp 

# check two operators are conflict 
def is_conflict(w1, w2):
	(wA, locA, pA) = (w1, w1.loc, w1.pid)
	(wB, locB, pB) = (w2, w2.loc, w2.pid)
	return (wA.sort() == WriteOp or wB.sort() == WriteOp) and ((locA ==locB))		

# collect a list of conflicting writes wrt memory operation rw
def conflict_writes(writes, rw):
	ret = []
	for w in writes:
		if is_conflict(w, rw):
			ret += [w]
	return ret

def SC_model(info = {}):

	# Relations
	spo = Function('spo', Opr, Opr, BoolSort()) 	# Significant program order
	sco = Function('sco', Opr, Opr, BoolSort())		# Significant conflict order
	
	# Helping_relation
	loopRel = Function('loopRel', Opr, Opr, BoolSort())	

	spo.domain = (lambda i: Opr)
	sco.domain = (lambda i: Opr)
	loopRel.domain = (lambda i: Opr) 

	rw1, rw2 = Consts('rw1 rw2', MemOp)
	a, b = 	Consts('a b', Opr)
	r = Const('r', ReadOp)
	w = Const('w', WriteOp)
	r1, r2 = Consts('r1 r2', ReadOp)
	w1, w2 = Consts('w1 w2', WriteOp)
	i, j = Consts('i j', Proc)

	# Conditions 
	sc_axioms = [
		# SPO Def
		ForAll([rw1, rw2],
			Implies(And(
				po(rw1, rw2), 
				# Not(conflict(rw1, rw2))
				Not(mem_access(rw1) == mem_access(rw2))
				),
				spo(rw1, rw2)) 
			),
		# SCO Def
		ForAll([rw1, rw2], 
			Implies(ico(rw1, rw2), sco(rw1, rw2))
			),
		ForAll([r1, r2, w], 
			Implies(
				And(ico(r1, w), ico(w, r2)),
				sco(r1, r2))
			),
		# Uniprocessor cond (RW -po-> W)
		ForAll([rw1, w, i],
			Implies(
				And(
					conflict(rw1, w),
					po(rw1, w),
				),
				xo(subOpr(rw1,i), subOpr(w, i)) 
				)
			),
		# Coherence (W -co'-> W)
		ForAll([w1, w2, i],
			Implies(
				And(
					conflict(w1, w2),
					ico(w1, w2),
					),
				xo(subOpr(w1,i), subOpr(w2, i)) 
				)
			),
		
		# LoopRel def 
		ForAll([rw1, rw2],
			If( Exists(a, And(sco(rw1, a), spo(a, rw2))), loopRel(rw1, rw2),
				If( Exists([a], And(loopRel(rw1,a), loopRel(a, rw2)) ) , 
					loopRel(rw1, rw2) , Not(loopRel(rw1, rw2)) )
				)
		),
		# not reflexive
		ForAll([rw1, rw2],
			Implies(loopRel(rw1,rw2), rw1 != rw2)
		),



		# # LoopRel def (Base case)
		# ForAll([rw1, rw2],
		# 	Implies(sco(rw1, rw2),
		# 		loopRel(rw1, rw2))
		# 	),
		# # LoopRel def (Inductive case)
		# ForAll([rw1, rw2,a, b, i],
		# 	Implies(
		# 		And(loopRel(rw1, a),
		# 			spo(a, b),
		# 			sco(b, rw2)
		# 			),
		# 		loopRel(rw1, rw2))
		# 	),


		# Multi-proc 1
		ForAll([w1, r, rw2, i],
			Implies(
				And(conflict(w1, rw2),
					ico(w1, r),
					po(r, rw2),
					),
				xo(subOpr(w1, i), subOpr(rw2, i)))
			),
		# Multi-proc 2
		ForAll([rw1, rw2, a, i],
			Implies(And(
					conflict(rw1, rw2),
					spo(rw1, a),
					loopRel(a, rw2),
					# spo(b, rw2),
					),
				xo(subOpr(rw1, i), subOpr(rw2, i)))
			),
		# Multi-proc 3
		ForAll([w1, r2, i, r, a],
			Implies(And(
					conflict(w1, r2),
					sco(w1, r),
					spo(r, a), 
					loopRel(a, r2),
					# spo(b, r2),
					),
				xo(subOpr(w1, i), subOpr(r2, i)))
			),
	]
	return sc_axioms

def TSO_model(info = {}):
	# Relations
	spo = Function('spo', Opr, Opr, BoolSort()) 	# Significant program order
	spo1 = Function('spo1', Opr, Opr, BoolSort()) 	# Significant program order spo'
	spo2 = Function('spo2', Opr, Opr, BoolSort()) 	# Significant program order spo''
	sco = Function('sco', Opr, Opr, BoolSort())		# Significant conflict order
	loopRel = Function('loopRel', Opr, Opr, BoolSort())	# Helping_relation

	spo.domain = (lambda i: Opr)
	spo1.domain = (lambda i: Opr)
	spo2.domain = (lambda i: Opr)
	sco.domain = (lambda i: Opr)
	loopRel.domain = (lambda i: Opr) 

	def spo_relation(info = {}):
		reads = info['read']
		writes = info['write']
		rmw = info['RMW']

		x, y = Consts('x y', MemOp)
		

		# spo'(X,Y) if ...
		#   R -po-> RW
		# 	W -po-> W
		# 	W -po-> MEMBAR(WR) -po-> R

		SPO = [ ForAll([x], Not( spo(x,x) )) ]
		SPO1 = [ ForAll([x], Not( spo1(x,x) )) ]
		SPO2 = [ ForAll([x], Not( spo2(x,x) )) ]

		write_p_rmw = writes #+ [(hw.atomic_write(a),l,i) for (a, l, i) in rmw]
		read_p_rmw = reads #+ [(hw.atomic_read(a),l,i) for (a, l, i) in rmw]
		atom_w = [w for (r, w) in rmw]
		
		rw1, rw2, rw3 = Consts('rw1 rw2 rw3', MemOp)
		r = Const('tempR', ReadOp)
		w1, w2 = Consts('tempW1 tempW2', WriteOp)
		wr = Const('wr_fence', MembarWR)
		st = Const('st_fence', STBar)

		SPO2 += [
			ForAll([rw1, rw2], 
				# R -po-> RW
				If(Exists([r], And(restrict(r, read_p_rmw), rw1 == read(r), po(r, rw2))), 
					spo2(rw1, rw2), 
				# W -po-> W 
				If(Exists([w1, w2], And(Not(w1 == w2), restrict(w1, write_p_rmw), restrict(w2, write_p_rmw), 
										rw1 == write(w1), rw2 == write(w2), po(w1, w2))),
					spo2(rw1, rw2),
				# W -po-> MEMBAR(WR) -po-> R
				If(Exists([w1, r, wr], And(restrict(w1, write_p_rmw), restrict(r, read_p_rmw), 
										rw1 == write(w1), rw2 == read(r),
										po(w1, wr), po(wr, r))), 
					spo2(rw1, rw2), 
				Not(spo2(rw1, rw2)))
				))
				)
		]

		SPO1 += [
			ForAll([rw1, rw2],
				# W (in RMW) -po-> R
				If( Exists([r,w1], And(
											# restrict(a_rmw, rmw), 
											# rw1 == write(hw.atomic_write(a_rmw)), 
											restrict(r, read_p_rmw), 
											restrict(w1, atom_w),
											rw2 == read(r),
											rw1 == write(w1),
											po(rw1, rw2))),
				spo1(rw1, rw2), Not(spo1(rw1, rw2)))
				)

		]

		memOps = [ MemOp.cast(rw) for rw in write_p_rmw + read_p_rmw]
		SPO += [
			ForAll([rw1, rw2],
				Implies( And(restrict(rw1, memOps), restrict(rw2, memOps)),
					If(spo1(rw1, rw2), spo(rw1, rw2),
					If(spo2(rw1, rw2), spo(rw1, rw2), 
					If(Exists([rw3], And(spo(rw1, rw3), spo(rw3, rw2)) ), spo(rw1, rw2), Not(spo(rw1, rw2))))
					) 
				)
			)
		]

		return SPO + SPO1 + SPO2
	def sco_relation(info):
		reads = info['read']
		writes = info['write']
		rmw = info['RMW']

		write_p_rmw = writes #+ [(hw.atomic_write(a),l,i) for (a, l, i) in rmw]
		read_p_rmw = reads #+ [(hw.atomic_read(a),l,i) for (a, l, i) in rmw]
		memOps = [ MemOp.cast(rw) for rw in write_p_rmw + read_p_rmw]

		x, y = Consts('x y', MemOp)
		r1, r2 = Consts('r1 r2', ReadOp)
		w = Const('w', WriteOp)

		SCO = [ ForAll([x], Not(sco(x,x))) ]

		SCO += [
			ForAll([x, y],
				If(And(restrict(x,memOps), restrict(y,memOps), co(x,y)), sco(x,y),
				If(Exists([r1,r2, w], And(Not(r1 == r2), restrict(r1, read_p_rmw), restrict(r2, read_p_rmw),
										restrict(w, write_p_rmw),
										read(r1) == x, read(r2) == y, co(x,w), co(w,y) )), 
					sco(x,y), Not(sco(x,y)))
				)
			)
		]

		return SCO
	# ------ variables 
	rw1, rw2, rw3 = Consts('rw1 rw2 rw3', MemOp)
	a, b = 	Consts('a b', Opr)
	r = Const('r', ReadOp)
	w = Const('w', WriteOp)
	r1, r2 = Consts('r1 r2', ReadOp)
	w1, w2 = Consts('w1 w2', WriteOp)
	i, j = Consts('i j', Proc)

	memb_wr = Const('membar_wr', MembarWR)

	# Conditions 
	tso_axioms = [		
		# % Uniproc RW -po-> W
		# xo(subOpr(X,I), subOpr(Y,I)) :- conflict(X,Y), subOpr(X,I), subOpr(Y,I), pOrder(X,Y), isWrite(Y), isRW(X).
		ForAll([rw1, w2, i],
			Implies(
				And(
					conflict(rw1, w2),
					po(rw1, w2),
				),
				xo(subOpr(rw1, i), subOpr(w2, i))
			)
		),

		# % Coherence W -co-> W 
		# xo(subOpr(X,I), subOpr(Y,I)) :- conflict(X,Y), subOpr(X,I), subOpr(Y,I), isWrite(X), isWrite(Y), co(X,Y).
		ForAll([w1, w2, i],
			Implies(
				And(
					conflict(w1, w2), 
					co(w1, w2),
				),
				xo(subOpr(w1, i), subOpr(w2, i))
			)
		),

		# % Multi - 1    W -co-> R -spo-> RW
		# xo(subOpr(W,I), subOpr(RW,I)) :- conflict(W,RW), subOpr(W,I), subOpr(RW,I), isWrite(W), isRead(R), isRW(RW), co(W,R), spo(R,RW). 
		ForAll([w1, rw2, i, r],
			Implies(
				And(
					conflict(w1, rw2),
					co(w1, r),
					spo(r, rw2),				
				),
				xo(subOpr(w1, i), subOpr(rw2, i))
			)
		),

		# LoopRel def 
		ForAll([rw1, rw2],
			If( Exists(a, And(sco(rw1, a), spo(a, rw2))), loopRel(rw1, rw2),
				If( Exists([a], And(loopRel(rw1,a), loopRel(a, rw2)) ) , 
					loopRel(rw1, rw2) , Not(loopRel(rw1, rw2)) )
				)
		),
		# not reflexive
		ForAll([rw1, rw2],
			Implies(loopRel(rw1,rw2), rw1 != rw2)
		),

		# % Multi - 2
		# % RW -spo-> { A -sco-> B -spo-> }+ RW *)
		# xo(subOpr(RW,I), subOpr(RW2,I)) :- conflict(RW,RW2), subOpr(RW,I), subOpr(RW2,I), isRW(RW), isRW(RW2), spo(RW,AA), loopRel(AA,BB), spo(BB,RW2). 
		ForAll([rw1, rw2, a, i],
			Implies(
				And(
					conflict(rw1, rw2),
					spo(rw1, a),
					loopRel(a, rw2),
					# spo(b, rw2),
				),
				xo(subOpr(rw1, i), subOpr(rw2, i))
			)
		),

		# % Multi - 3
		# %% W -sco-> R -spo-> { A -sco-> B -spo-> }+ R
		# xo(subOpr(W,I), subOpr(R2,I)) :- conflict(W,R2), subOpr(W,I), subOpr(R2,I), isWrite(W), isRead(R), isRead(R2), sco(W,R), spo(R,AA), loopRel(AA,BB), spo(BB,R2). 
		ForAll([w1, r2, i, a, r],
			Implies(
				And(
					conflict(w1, r2),
					sco(w1, r),
					spo(r, a),
					loopRel(a, r2),
					# spo(b, r2),  
				),
				xo(subOpr(w1, i), subOpr(r2, i))
			)
		),
	]
	return (tso_axioms) + spo_relation(info) + sco_relation(info)

def PSO_model(info = {}):

	# Relations
	spo = Function('spo', Opr, Opr, BoolSort()) 	# Significant program order
	spo1 = Function('spo1', Opr, Opr, BoolSort()) 	# Significant program order spo'
	spo2 = Function('spo2', Opr, Opr, BoolSort()) 	# Significant program order spo''
	sco = Function('sco', Opr, Opr, BoolSort())		# Significant conflict order
	loopRel = Function('loopRel', Opr, Opr, BoolSort())	# Helping_relation

	spo.domain = (lambda i: Opr)
	spo1.domain = (lambda i: Opr)
	spo2.domain = (lambda i: Opr)
	sco.domain = (lambda i: Opr)
	loopRel.domain = (lambda i: Opr) 

	def spo_relation(info = {}):
		reads = info['read']
		writes = info['write']
		rmw = info['RMW']

		x, y = Consts('x y', MemOp)
		

		# spo'(X,Y) if ...
		#   R -po-> RW
		# 	W -po-> W
		# 	W -po-> MEMBAR(WR) -po-> R

		SPO = [ ForAll([x], Not( spo(x,x) )) ]
		SPO1 = [ ForAll([x], Not( spo1(x,x) )) ]
		SPO2 = [ ForAll([x], Not( spo2(x,x) )) ]

		write_p_rmw = writes #+ [(hw.atomic_write(a),l,i) for (a, l, i) in rmw]
		read_p_rmw = reads #+ [(hw.atomic_read(a),l,i) for (a, l, i) in rmw]
		atom_w = [w for (r, w) in rmw]
		
		rw1, rw2, rw3 = Consts('rw1 rw2 rw3', MemOp)
		r = Const('tempR', ReadOp)
		w1, w2 = Consts('tempW1 tempW2', WriteOp)
		wr = Const('wr_fence', MembarWR)
		st = Const('st_fence', STBar)

		SPO2 += [
			ForAll([rw1, rw2], 
				# R -po-> RW
				If(Exists([r], And(restrict(r, read_p_rmw), rw1 == read(r), po(r, rw2))), 
					spo2(rw1, rw2), 
				# W -po-> STBAR -po-> W 
				If(Exists([w1, w2, st], And(Not(w1 == w2), restrict(w1, write_p_rmw), restrict(w2, write_p_rmw), 
										rw1 == write(w1), rw2 == write(w2), po(w1, st), po(st, w2))),
					spo2(rw1, rw2),
				# W -po-> MEMBAR(WR) -po-> R
				If(Exists([w1, r, wr], And(restrict(w1, write_p_rmw), restrict(r, read_p_rmw), 
										rw1 == write(w1), rw2 == read(r),
										po(w1, wr), po(wr, r))), 
					spo2(rw1, rw2), 
				Not(spo2(rw1, rw2)))
				))
				)
		]

		SPO1 += [
			ForAll([rw1, rw2],
				# W (in RMW) -po-> R
				If( Exists([r,w1], And(
											# restrict(a_rmw, rmw), 
											# rw1 == write(hw.atomic_write(a_rmw)), 
											restrict(r, read_p_rmw), 
											restrict(w1, atom_w),
											rw2 == read(r),
											rw1 == write(w1),
											po(rw1, rw2))),
				spo1(rw1, rw2), Not(spo1(rw1, rw2)))
				)

		]

		memOps = [ MemOp.cast(rw) for rw in write_p_rmw + read_p_rmw]
		SPO += [
			ForAll([rw1, rw2],
				Implies( And(restrict(rw1, memOps), restrict(rw2, memOps)),
					If(spo1(rw1, rw2), spo(rw1, rw2),
					If(spo2(rw1, rw2), spo(rw1, rw2), 
					If(Exists([rw3], And(spo(rw1, rw3), spo(rw3, rw2)) ), spo(rw1, rw2), Not(spo(rw1, rw2))))
					) 
				)
			)
		]

		return SPO + SPO1 + SPO2
	def sco_relation(info):
		reads = info['read']
		writes = info['write']
		rmw = info['RMW']

		write_p_rmw = writes #+ [(hw.atomic_write(a),l,i) for (a, l, i) in rmw]
		read_p_rmw = reads #+ [(hw.atomic_read(a),l,i) for (a, l, i) in rmw]
		memOps = [ MemOp.cast(rw) for rw in write_p_rmw + read_p_rmw]

		x, y = Consts('x y', MemOp)
		r1, r2 = Consts('r1 r2', ReadOp)
		w = Const('w', WriteOp)

		SCO = [ ForAll([x], Not(sco(x,x))) ]

		SCO += [
			ForAll([x, y],
				If(And(restrict(x,memOps), restrict(y,memOps), co(x,y)), sco(x,y),
				If(Exists([r1,r2, w], And(Not(r1 == r2), restrict(r1, read_p_rmw), restrict(r2, read_p_rmw),
										restrict(w, write_p_rmw),
										read(r1) == x, read(r2) == y, co(x,w), co(w,y) )), 
					sco(x,y), Not(sco(x,y)))
				)
			)
		]

		return SCO
	# ------ variables 
	rw1, rw2, rw3 = Consts('rw1 rw2 rw3', MemOp)
	a, b = 	Consts('a b', Opr)
	r = Const('r', ReadOp)
	w = Const('w', WriteOp)
	r1, r2 = Consts('r1 r2', ReadOp)
	w1, w2 = Consts('w1 w2', WriteOp)
	i, j = Consts('i j', Proc)

	memb_wr = Const('membar_wr', MembarWR)

	# Conditions 
	pso_axioms = [		
		# % Uniproc RW -po-> W
		# xo(subOpr(X,I), subOpr(Y,I)) :- conflict(X,Y), subOpr(X,I), subOpr(Y,I), pOrder(X,Y), isWrite(Y), isRW(X).
		ForAll([rw1, w2, i],
			Implies(
				And(
					conflict(rw1, w2),
					po(rw1, w2),
				),
				xo(subOpr(rw1, i), subOpr(w2, i))
			)
		),

		# % Coherence W -co-> W 
		# xo(subOpr(X,I), subOpr(Y,I)) :- conflict(X,Y), subOpr(X,I), subOpr(Y,I), isWrite(X), isWrite(Y), co(X,Y).
		ForAll([w1, w2, i],
			Implies(
				And(
					conflict(w1, w2), 
					co(w1, w2),
				),
				xo(subOpr(w1, i), subOpr(w2, i))
			)
		),

		# % Multi - 1    W -co-> R -spo-> RW
		# xo(subOpr(W,I), subOpr(RW,I)) :- conflict(W,RW), subOpr(W,I), subOpr(RW,I), isWrite(W), isRead(R), isRW(RW), co(W,R), spo(R,RW). 
		ForAll([w1, rw2, i, r],
			Implies(
				And(
					conflict(w1, rw2),
					co(w1, r),
					spo(r, rw2),				
				),
				xo(subOpr(w1, i), subOpr(rw2, i))
			)
		),

		# LoopRel def 
		ForAll([rw1, rw2],
			If( Exists(a, And(sco(rw1, a), spo(a, rw2))), loopRel(rw1, rw2),
				If( Exists([a], And(loopRel(rw1,a), loopRel(a, rw2)) ) , 
					loopRel(rw1, rw2) , Not(loopRel(rw1, rw2)) )
				)
		),
		# not reflexive
		ForAll([rw1, rw2],
			Implies(loopRel(rw1,rw2), rw1 != rw2)
		),

		# % Multi - 2
		# % RW -spo-> { A -sco-> B -spo-> }+ RW *)
		# xo(subOpr(RW,I), subOpr(RW2,I)) :- conflict(RW,RW2), subOpr(RW,I), subOpr(RW2,I), isRW(RW), isRW(RW2), spo(RW,AA), loopRel(AA,BB), spo(BB,RW2). 
		ForAll([rw1, rw2, a, i],
			Implies(
				And(
					conflict(rw1, rw2),
					spo(rw1, a),
					loopRel(a, rw2),
					# spo(b, rw2),
				),
				xo(subOpr(rw1, i), subOpr(rw2, i))
			)
		),

		# % Multi - 3
		# %% W -sco-> R -spo-> { A -sco-> B -spo-> }+ R
		# xo(subOpr(W,I), subOpr(R2,I)) :- conflict(W,R2), subOpr(W,I), subOpr(R2,I), isWrite(W), isRead(R), isRead(R2), sco(W,R), spo(R,AA), loopRel(AA,BB), spo(BB,R2). 
		ForAll([w1, r2, i, a, r],
			Implies(
				And(
					conflict(w1, r2),
					sco(w1, r),
					spo(r, a),
					loopRel(a, r2),
					# spo(b, r2),  
				),
				xo(subOpr(w1, i), subOpr(r2, i))
			)
		),
	]
	return (pso_axioms) + spo_relation(info) + sco_relation(info)

class encoder(encodingFW):

	def supportedModels(self):
		return ['SC', 'TSO', 'PSO']
	
	def getEvent(self, op):
		if op.sort() == STBar:
			# print Opr.cast(FenceOp.cast(op))
			# return Opr.cast(FenceOp.cast(op))
			return None
		else:
			return (MemOp.cast(op))
	def new_write(self, var, exp, pid):
		name = 'write_' + str(self.info['EventCnt'])
		write = Const(name, WriteOp)
		
		write.eid = self.info['EventCnt']
		write.loc = var 
		write.pid = pid 

		self.info['EventCnt'] = self.info['EventCnt'] + 1


		pid = Const('P'+str(pid), Proc)
		self.info['CS'] += [
			write_val(write) == exp,
			mem_access(write) == var, 
			issue_proc(write) == pid
		]

		return write
	def new_read(self, var, exp, pid):
		name = 'read_' + str(self.info['EventCnt'])
		read = Const(name, ReadOp)

		read.eid = self.info['EventCnt']
		read.loc = exp 
		read.pid = pid

		self.info['EventCnt'] = self.info['EventCnt'] + 1
		

		pid = Const('P'+str(pid), Proc)
		
		self.info['CS'] += [
			var == return_val(read),
			mem_access(read) == exp, 
			issue_proc(read) == pid
		]		
		return read
	def new_loc(self, addr):
		return Const(str(addr), Loc)

	def new_branch(self, pid):
		# raise NotImplementedError()
		return None

	def specialEncode(self, i, pid):
		if isinstance(i, STBarFence):
			eidCnt = self.info['EventCnt']
			# fence = Fence(eidCnt, FenceType.STBar, pid)
			fence = Const('fence_'+str(eidCnt), STBar)
			self.info['EventCnt'] = self.info['EventCnt'] + 1
			fence.eid = eidCnt
			fence.pid = pid
			return fence
		elif isinstance(i, MEM_WR_Fence):
			eidCnt = self.info['EventCnt']
			fence = Const('fence_'+str(eidCnt), MembarWR)
			fence.eid = eidCnt
			fence.pid = pid
			self.info['EventCnt'] = self.info['EventCnt'] + 1
			return fence
		return None 

	def encodeElement(self, e):

		assert(isinstance(e, Exp) or isinstance(e, Register) or type(e) == int or type(e) == bool)
		
		if type(e) == int or type(e) == bool:
			return e
		elif isinstance(e, Register):
			return Int(str(e))
		# elif isinstance(e, Register):
		# 	if not(str(e) in info['Reg'].keys()):
		# 		info['Reg'][str(e)] = herd.Reg(info['RegCnt'])
		# 		info['RegCnt'] += 1
		# 	return (info['Reg'][str(e)], info)
		elif isinstance(e, Location):
			if not(e.address in self.info['Loc'].keys()):
				addrLoc = Int(str(e.address))
				self.info['Loc'][e.address] = self.new_loc(addrLoc) # InitLoc(addrLoc)
			return self.info['Loc'][e.address]
		elif isinstance(e, ifExp):
			# val := (cond)?1:0
			# r1 << val 
			return None
		elif isinstance(e, undefinedExp):
			return FreshInt()
		elif isinstance(e, Exp):
			return self.encodeExp(e)

		return None

	def encodeOpr(self, i):
		assert(isinstance(i, Operation))
		encodeOp = None 
		pid = self.info['Pid']

		if isinstance(i, WriteAssn) and isinstance(i.var, Location):		
			exp = self.encodeElement(i.exp)
			var = self.encodeElement(i.var)
			encodeOp = self.new_write(var, exp, pid)
			
		elif isinstance(i, ReadAssn) and isinstance(i.exp, Location):
			var = self.encodeElement(i.var)
			exp = self.encodeElement(i.exp)
			encodeOp = self.new_read(var, exp, pid)
		elif isinstance(i, Assignment):
			var = self.encodeElement(i.var)
			if not isinstance(i.exp, ifExp):
				exp = self.encodeElement(i.exp)
				self.info['CS'] += [var == exp]
			else:
				# val := (cond)?1:0
				cond = self.encodeElement(i.exp.cond)
				tExp = self.encodeElement(i.exp.t_exp)
				fExp = self.encodeElement(i.exp.f_exp)
				self.info['CS'] += [ Implies(cond, var == tExp), 
								Implies(Not(cond), var == fExp) ]
		elif isinstance(i, fenceStm):
			encodeOp = self.specialEncode(i, pid)
			# print '&&&', encodeOp, i.__class__
		elif isinstance(i, branchOp):
			encodeOp = self.new_branch(pid)
		elif isinstance(i, RmwStm):
			assert(False)
		else:
			# print i
			assert(False)
		return encodeOp

	def encodeSpecific(self):
		self.info['read'] = [ r for r in self.info['Ev'] if r.sort() == ReadOp ]
		self.info['write'] = [ w for w in self.info['Ev'] if w.sort() == WriteOp ]

		# realize po
		for x in self.info['Ev']:
			for y in self.info['Ev']:
				self.info['CS'] += [ po(x,y) if (x.eid,y.eid) in self.info['poS'] else Not(po(x,y)) ]

		# initial_location
		for L in self.info['Loc'].values():
			self.info['CS'] += [initial_value(L) == 0]



		# underlying axioms
		axioms = self.based_axioms()
		axioms += self.model_axioms()
		axioms += self.additional_axioms()
		if len(self.info['Loc'].values()) > 1:
			axioms += [Distinct(self.info['Loc'].values())]

		# return False
		return And(And(self.info['CS'] + axioms),Not(And(self.info['PS'])))

	def based_axioms(self):

		# Conflict 
		def conflict_def(w1, w2):
			(wA, locA, pA) = (w1, w1.loc, w1.pid)
			(wB, locB, pB) = (w2, w2.loc, w2.pid)
			if wA.sort() == WriteOp or wB.sort() == WriteOp:
				return (conflict(wA, wB) == eq(locA,locB))
			else: 
				return (Not(conflict(wA, wB)))

		conflict_manual_def = []
		# write = info['MemOp']['write']
		# read = info['MemOp']['read']
		rmwList = self.info['RMW']

		memOp = [e for e in self.info['Ev'] if is_RW(e)]
		conflict_manual_def += [ conflict_def(w1, w2) for (w1, w2) in itertools.permutations(memOp, 2) if is_RW(w1) and is_RW(w2)]
		conflict_manual_def += [ Not(conflict(w1,w1)) for w1 in memOp  if is_RW(w1) ]
	
		
		# -co-> definition
		def co_def(w1, w2):
			(wA, locA, pA) = (w1, w1.loc, w1.pid)
			(wB, locB, pB) = (w2, w2.loc, w2.pid)
			i = Const('i', Proc)
			if (wA.sort() == WriteOp or wB.sort() == WriteOp) and (locA == locB):
				return (co(wA, wB) == Exists([i],xo(subOpr(wA,i), subOpr(wB,i))))
			else:
				return Not(co(wA, wB))

		# -co'-> definition
		def ico_def(w1, w2):
			(wA, locA, pA) = (w1, w1.loc, w1.pid)
			(wB, locB, pB) = (w2, w2.loc, w2.pid)
			i = Const('i', Proc)
			if (wA.sort() == WriteOp or wB.sort() == WriteOp) and (locA == locB) and not (pA == pB):
				return (ico(wA, wB) == Exists([i],xo(subOpr(wA,i), subOpr(wB,i))))
			else:
				return Not(ico(wA, wB))

		conflict_manual_def += [ co_def(w1, w2) for (w1, w2) in itertools.permutations(memOp, 2)]
		conflict_manual_def += [ Not(co(w1, w1)) for w1 in memOp]
		conflict_manual_def += [ ico_def(w1, w2) for (w1, w2) in itertools.permutations(memOp, 2)]
		conflict_manual_def += [ Not(ico(w1, w1)) for w1 in memOp]

		rw1, rw2 = Consts('rw1 rw2', MemOp)
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
		for (rmw_r, rmw_w) in rmwList:
			(loc, pi ) = (rmw_r.loc, rmw_r.pid)
			pi = Const('P' + str(pi), Proc)
			axioms_atomic += [
				ForAll(w, 
						Implies(
							(conflict(rmw_w, w)),
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
			+ partial_order_axioms(po) 
			+ partial_order_axioms(xo)
			+ addition_order
			+ axioms_atomic 
			)

	def model_axioms(self):
		if self.model == 'SC':
			return SC_model()
		elif self.model == 'TSO':
			return TSO_model(self.info)
		elif self.model == 'PSO':
			return PSO_model(self.info)
		return []

	def additional_axioms(self):
		xo_axioms = self.generate_xo()
		return_axioms = self.generate_return_value_cond()
		# print return_axioms
		# assert(False)
		return xo_axioms + return_axioms

	def generate_xo(self):
		write = self.info['write']
		read = self.info['read']
		# print self.info['Pid']
		proc = [Const('P'+str(i), Proc) for i in range(0, self.info['Pid'])]
		
		listSubOprW = [subOpr(w, i) for i in proc for w in write ]
		# print read
		listSubOprR = [subOpr(r, Const('P'+str(r.pid), Proc)) for r in read ]

		listAxioms = []
		listAxioms += [
				Xor(xo(x,y), xo(y,x)) 
			for (x,y) in itertools.combinations(listSubOprW, 2)]
		listAxioms += [
				Xor(xo(x,y), xo(y,x)) 
			for x in listSubOprW for y in listSubOprR]

		return listAxioms 

	def generate_return_value_cond(self):
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

		read = self.info['read']
		write = self.info['write']

		return_axioms = []
		for y in read:
			(l, k) = (y.loc, Const('P'+str(y.pid), Proc))
			writes_conflict_r = conflict_writes(write, y)
			return_axioms += [
				If( And(no_write_cond(y,k,0, writes_conflict_r), no_write_cond(y,k,1, writes_conflict_r)), 
						# return_val(y) == initial_value(mem_access(y)) 
						return_val(y) == 0
						,If(no_write_cond(y,k,0, writes_conflict_r), 
							Exists([wj], 
								And(restrict(wj,writes_conflict_r),		# w in Ws(conflict r)
									conflict(wj, y),							# confirm conflict again
									xo(subOpr(wj, k), subOpr(y, k)),			# wj(i) -xo-> r(i)
									ConseqXO(wj, y),
									# consecutive_write(y,wj,k,1), 				
									(return_val(y) == write_val(wj)) )), 
						Exists([wj], 
							And(restrict(wj,writes_conflict_r),			# w in Ws(conflict r)
								conflict(wj, y),								# confirm conflict again
								xo( subOpr(y,k), subOpr(wj, k) ),				# r(i) -xo-> wj(i)
								ConseqPO(wj, y), 			
								(return_val(y)) == write_val(wj)))
					)
				)
			]
		conseq_po = []
		conseq_xo = []
		for r in read:
			locA = r.loc
			i = Const('P'+str(r.pid), Proc)

			writes_conflict_r = conflict_writes(write, r)
			for w in writes_conflict_r:
				locB = w.loc 
				j = Const('P'+str(w.pid), Proc)

				retPo = [po(w,r)] 	# w -po-> r
				retXo = [True]
				subOprW = subOpr(w,i)
				subOprR = subOpr(r,i)	
				for wj in writes_conflict_r:
					l = wj.loc 
					k = Const('P'+str(wj.pid), Proc)
					if(not eq(w,wj)):
						subOprWj = subOpr(wj, i)
						retPo += [Xor( And( po(wj, w), po(wj, r) ), 
											And( po(w, wj), po(r, wj)))]
						retXo += [Xor( And(xo(subOprWj, subOprR), xo(subOprWj, subOprW) ),
										 And(xo(subOprR, subOprWj), xo(subOprW, subOprWj) ) )]
				conseq_po += [ConseqPO(w,r) == And(retPo)]
				conseq_xo += [ConseqXO(w,r) == And(retXo)]
			
		# print conseq_po
		return return_axioms + conseq_po + conseq_xo
		






		
