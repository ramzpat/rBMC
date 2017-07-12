# herding cat framework

from encodingFW import *

# Abstract model def 
Proc = 		IntSort()			 			# Processor
Instr = 	DeclareSort('Instr')			# Instruction 


Val = Datatype('Val')
Val.declare('undifined')
Val.declare('temp', ('id', IntSort()))
Val.declare('int', ('val', IntSort()))
Val.declare('reg', ('rid', IntSort()))
Val = Val.create()
Reg = Val.reg
Temp = Val.temp

# addrLoc = Function('addrLoc', Loc, IntSort())

Loc = Datatype('Loc')
Loc.declare('undefined')
Loc.declare('loc', ('addr', IntSort()))
Loc = Loc.create()
InitLoc = Loc.loc

initLocVal = Function('initLocVal', Loc, IntSort())

def is_reg(e):
	return eq(e.decl(), Reg)
def is_intVal(e):
	return eq(e.decl(), Val.int)

Event =		Datatype('Event')
Event.declare('undefined')
Event.declare('event', 		('eid', IntSort()), ('pid', Proc))
Event.declare('read',  		('eid', IntSort()), ('loc', Loc), ('dest', IntSort()), ('pid', Proc))
Event.declare('write', 		('eid', IntSort()), ('loc', Loc), ('val', IntSort()), ('pid', Proc))
Event.declare('read_reg', 	('eid', IntSort()), ('reg', Val), ('dest', IntSort()), ('pid', Proc) )
Event.declare('write_reg', 	('eid', IntSort()), ('reg', Val), ('val', IntSort()), ('pid', Proc))
Event.declare('branch', ('eid', IntSort()), ('pid', Proc))
Event.declare('fence', 		('eid', IntSort()), ('ftype', IntSort()), ('pid', Proc))

# Load-lock / Store-condition Semantics
# Event.declare('write_resv', ('eid', IntSort()), ('loc', Loc))
# Event.declare('read_resv', )



Event = Event.create()
ConstEvent = Event.event
ReadOp = Event.read
WriteOp = Event.write
WriteReg = Event.write_reg
ReadReg = Event.read_reg
Branch = Event.branch
Fence = Event.fence

def enum(*sequential, **named):
    enums = dict(zip(sequential, range(len(sequential))), **named)
    return type('Enum', (), enums)

FenceType = enum('STBar', 'MEMBAR_WR', 'DMB', 'DSB')


# additional fence
class STBarFence(fenceStm):
	def __str__(self):
		return 'stbar()' 

class MEM_WR_Fence(fenceStm):
	def __str__(self):
		return 'MEMBAR(WR)'

class DMB(fenceStm):
	def __str__(self):
		return 'DMB()'

class DSB(fenceStm):
	def __str__(self):
		return 'DSB()'

def isWrite(e):
	return eq(e.decl(), WriteOp)
def isRead(e):
	return eq(e.decl(), ReadOp)
def isFence(e):
	return eq(e.decl(), Event.fence)
def isRW(rw):
	return isRead(rw) or isWrite(rw)

def isReadReg(e):
	return eq(e.decl(), ReadReg)
def isWriteReg(e):
	return eq(e.decl(), WriteReg)

def isBranch(e):
	return eq(e.decl(), Branch)

# Wrap function for subsort 
def subsort_f(sort1, sort2):
	f_sort = Function('wrap_'+str(sort1)+'_'+str(sort2), sort1, sort2)
	return f_sort 
def samePid(e1, e2):
	return ((e1.pid == e2.pid) or (e1.pid == 0) or (e2.pid == 0))




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

def concat_relation(a, b):
	a = set(a)
	b = set(b)
	new_relations = set((x,j)  for (x,y) in a for (i,j) in b if (y == i))
	return new_relations


def restrict(e, sets = []):
	return Or([e == i for i in sets ])

# transitive (r+)
# input a relation r
# return a relatoin r+ and axioms for transitive closure
def transitive(r_name, r, Set = []):
	domX = r.domain(0)
	domY = r.domain(1)

	trans_r = Function(r_name, domX, domY, BoolSort())

	x = Const('x', domX)
	y = Const('y', domY)
	z = Const('z', domY)

	return (trans_r, 
			[ForAll([x,y], trans_r(x,y) == Or(r(x,y),
											(Exists([z], And(restrict(z, Set, Event), trans_r(x,z), trans_r(z,y))))
											))])

def seqRelation(r_name, r1, r2):
	dom = r1.domain(0)
	seqR = Function(r_name, dom, dom, BoolSort())
	x, y, z = Consts('x y z', dom)
	return (seqR,
		[ForAll([x,z], seqR(x,z) == Exists([y], And(r1(x,y),r2(y,z)) ))]
		)


# acyclic / irreflexive
# def acyclic(name, r, sets = []):
# 	dom = r.domain(0)
# 	x, y = Consts('x y', dom)
# 	(r_trans,axiom) = transitive(name, r, sets)
# 	return (r_trans, axiom + [Not(Exists([x], r_trans(x,x) ))])


# Execution (E, po, rf, co)
# co - coherrence 
# initial write must the first write
# total order among conflicting writes 
# sc operation : write appears in co if condition satisfy
def conflict_order(Ev = [], scWrites = []):
	co = Function('co', Event, Event, BoolSort())
	axioms = []
	for e1 in Ev:
		for e2 in Ev:
			# if eq(e1.target, e2.target) and not(eq(e1.arg(0),e2.arg(0))):
			# 	print str((e1,e2)) + ': ' + str(eq(e1.target, e2.target))
			if not(e1 in scWrites) and not(e2 in scWrites):
				axioms += [(
					co(e1, e2) == (
						And(Distinct(e1, e2),
							Not(co(e2, e1)),
							e1.target == e2.target
							)
						if not(eq(e1.arg(0),e2.arg(0))) and isWrite(e1) and isWrite(e2) and e2.pid != 0 else False
						)
					)]
			# else: 

			# if not(eq(e1.arg(0),e2.arg(0))) and isWrite(e1) and isWrite(e2) and e2.pid != 0:
			# 	print e1, e2
	return (co, And(axioms))

# rf - one to many
def read_from(Ev = []):
	def candidate_writes(r, Ev = []):
		write =[w for w in Ev if isWrite(w) and eq(w.target, r.target) ]
		# print locB
		# candidate_w = [ (w,locA,pA) for (w,locA,pA) in write if (eq(locA, locB))]
		return write

	# rf : W x R relation
	e = Const('e', Event)
	rf = Function('rf', Event, Event, BoolSort())
	# s.register_relation(rf)
	axiom = []
	for e1 in Ev:
		if isRead(e1):
			cWrite = candidate_writes(e1, Ev)
			# print e1, cWrite
			axiom += [(Or([rf(w, e1) for w in cWrite ]))]
			# rf-val
			# print e1, cWrite
			axiom += [(And([
				Implies(rf(w, e1), w.val == e1.val)
				for w in cWrite
				]))]
		else:
			axiom += [(ForAll(e, Not(rf(e,e1))))]

	return (rf, And(axiom))

def iico_relation(S = [], Ev = []):
	# (iico, axiom) = relation('iico', Event, S)
	# s.add(axiom)

	# prepare for transitivity
	idS = []
	EvID = [0 for i in range(0, len(Ev))]
	for (i, j) in S:
		idS += [(i.eid, j.eid)]
		EvID[i.eid] = i 
		EvID[j.eid] = j	
		
	idS = transitive_closure(idS)

	iico = Function('iico', Event, Event, BoolSort())
	iicoSet = []
	axiom = []
	for e1 in Ev:
		for e2 in Ev:
			if (e1.eid, e2.eid) in idS:
				axiom += [( iico(e1, e2) )]
				iicoSet += [(e1.eid, e2.eid)]
			else:
				axiom += [(Not(iico(e1, e2)))]

	return (iico, iicoSet, And(axiom))

def rf_reg_relation(Ev = []):
	def candidate_writes(r, Ev = []):
		write =[w for w in Ev if isWriteReg(w) and eq(w.target, r.target) ]
		return write

	# rf : W-reg x R-reg relation
	e = Const('e', Event)
	rf_reg = Function('rf-reg', Event, Event, BoolSort())
	rf_regSet = []
	axiom = []
	for e1 in Ev:
		if isReadReg(e1):
			cWrite = candidate_writes(e1, Ev)
			# print e1, cWrite[0]
			# print len(cWrite)
			# try:
			assert(len(cWrite) == 1)
			# except AssertionError:
			# 	print e1, cWrite[0]
			# 	print len(cWrite)
			# 	assert(False)

			# there are only one correspond write in ssa form
			axiom += [(rf_reg(cWrite[0], e1))]
			# fix bug ?
			axiom += [(Not(rf_reg(ee, e1))) for ee in Ev if cWrite[0].eid != ee.eid ]
			# rf-val
			axiom += [(cWrite[0].val == e1.val)]
			rf_regSet += [(cWrite[0].eid, e1.eid)]
			# rf-loc
		else:
			axiom += [(ForAll(e, Not(rf_reg(e,e1))))]
	# print And(axiom)
	return (rf_reg, rf_regSet, And(axiom))

# fr - fromread (fixed point) 
def from_read(rf, co):
	fr = Function('fr', Event, Event, BoolSort())
	e1, e2, e3 = Consts('e1 e2 e3', Event)
	axiom = ( ForAll([e1, e2, e3], Implies( And(rf(e2, e1), co(e2, e3), Distinct(e1, e3)), fr(e1, e3) ) ) )
	return (fr, axiom)

# constraining 
def acyclic(*rel):
	trans = Function('acyclic' + str(rel), Event, Event, BoolSort())
	# print trans

	e1, e2, e3 = Consts('e1 e2 e3', Event)
	
	axiom = []
	for r in rel:
		# s.rule(trans(e1, e2), r(e1, e2))
		axiom.append( ForAll([e1, e2], Implies(r(e1, e2), trans(e1, e2)) ))
	# s.rule(trans(e1, e2), [trans(e1, e3), trans(e3, e2)])

	axiom.append(ForAll([e1, e2, e3], Implies(And(trans(e1, e2), trans(e2, e3)), trans(e1, e3)) ))
	axiom.append(ForAll(e1, Not(trans(e1, e1))))
	# s.vars = []
	return (trans, And(axiom))

def irreflexive(s, r):
	e = Const('e', Event)
	s.add(ForAll(e, Not(r(e,e))))
	return s

def empty(s, r):
	empty = Function('empty_' + str(r), Event, Event, BoolSort())
	e1, e2 = Consts('e1 e2', Event)
	s.add(ForAll([e1, e2], Not(e1, e2)))
	return (s, r)

def sc_constraints(po, rf, fr, co, Ev = [], RMW = []):
	# sc.cat
	# SC ----------
	rmw = Function('rmw', Event, Event, BoolSort())			
	axiom = []
	axiom += ([(rmw(e1, e2) if (e1, e2) in RMW else Not(rmw(e1,e2)) ) for e1 in Ev for e2 in Ev])

	rfe = Function('rfe', Event, Event, BoolSort())
	rfi = Function('rfi', Event, Event, BoolSort())
	fre = Function('fre', Event, Event, BoolSort())
	coe = Function('coe', Event, Event, BoolSort())

	for e1 in Ev:
		for e2 in Ev:
			axiom.append(rfe(e1, e2) == And(rf(e1,e2), Not(e1.pid == e2.pid)))
			axiom.append(rfi(e1, e2) == And(rf(e1,e2), (e1.pid == e2.pid)))
			axiom.append(fre(e1, e2) == And(fr(e1,e2), Not(e1.pid == e2.pid)))
			axiom.append(coe(e1, e2) == And(co(e1,e2), Not(e1.pid == e2.pid)))

	# (* Atomic *)
	# empty rmw & (fre;coe) as atomic
	e1, e2, e3 = Consts('e1 e2 e3', Event)
	frecoe = Function('fre;coe', Event, Event, BoolSort())
	axiom.append( ForAll([e1, e2, e3], Implies( And(fre(e1, e3), coe(e3, e2)), frecoe(e1, e2) )) )
	axiom.append( ForAll([e1, e2], Not( And( rmw(e1,e2), frecoe(e1, e2) ) )))

	
	# (* Sequential consistency *)
	# acyclic po | fr | rf | co as sc
	(trans, acyclic_axiom) = (acyclic(po, fr, rf, co))
	# self.info['acyclic'] = trans
	# print acyclic_axiom
	return And(And(axiom), acyclic_axiom)


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
	pass 

def PSO_model(info = {}):
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
		return ['SC', 'TSO', 'PSO', 'ARM']
	
	def getEvent(self, op):
		return (op)

	def new_write(self, var, exp, pid):
		eidCnt = self.info['EventCnt']
		v = exp
		if is_reg(var):
			write = WriteReg(eidCnt, var, v, pid ) #Const(name, WriteReg)	
		else: 
			write = WriteOp(eidCnt, var, v, pid) #Const(name, WriteOp)
		write.eid = eidCnt
		self.info['EventCnt'] = self.info['EventCnt'] + 1
		write.target = var
		write.val = exp
		write.pid = pid
		return write

	def new_read(self, var, exp, pid):
		eidCnt = self.info['EventCnt']
		if is_reg(exp):
			read = ReadReg(eidCnt, exp, var, pid) #Const(name, ReadReg)
		else:
			read = ReadOp(eidCnt, exp, var, pid) #Const(name, ReadOp)
		read.eid = eidCnt
		self.info['EventCnt'] = self.info['EventCnt'] + 1
		read.target = exp
		read.val = var
		read.pid = pid
		return read

	def new_loc(self, addr):
		loc = Const(addr, Loc)
		# global_axioms += [idLoc(loc) == id_loc]
		# id_loc += 1
		return loc

	def new_branch(self, pid):
		eidCnt = self.info['EventCnt']
		br = Branch(eidCnt, pid)
		br.eid = eidCnt
		br.pid = pid
		br.target = None
		self.info['EventCnt'] = self.info['EventCnt'] + 1
		return br 

	def specialEncode(self, i, pid):
		if isinstance(i, STBarFence):
			eidCnt = self.info['EventCnt']
			fence = Fence(eidCnt, FenceType.STBar, pid)
			self.info['EventCnt'] = self.info['EventCnt'] + 1
			fence.eid = eidCnt
			fence.pid = pid
			return fence
		elif isinstance(i, MEM_WR_Fence):
			eidCnt = self.info['EventCnt']
			fence = Fence(eidCnt, FenceType.MEMBAR_WR, pid)
			fence.eid = eidCnt
			fence.pid = pid
			self.info['EventCnt'] = self.info['EventCnt'] + 1
			return fence
		return None 

	def encodeElement(self, e):
		assert(isinstance(e, Exp) or isinstance(e, Register) or type(e) == int or type(e) == bool)
		
		if type(e) == int or type(e) == bool:
			return e
		elif isinstance(e, TempReg):
			return Int(str(e))
		elif isinstance(e, Register):
			if not(str(e) in self.info['Reg'].keys()):
				self.info['Reg'][str(e)] = Reg(self.info['RegCnt'])
				self.info['RegCnt'] += 1
			return self.info['Reg'][str(e)]
		elif isinstance(e, Location):
			if not(e.address in self.info['Loc'].keys()):
				addrLoc = Int(str(e.address))
				self.info['Loc'][e.address] = InitLoc(addrLoc)
			return self.info['Loc'][e.address]
		elif isinstance(e, Resv):
			assert(False)
			pass
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

		if isinstance(i, WriteAssn):		
			exp = self.encodeElement(i.exp)
			var = self.encodeElement(i.var)
			encodeOp = self.new_write(var, exp, pid)
			
		elif isinstance(i, ReadAssn):
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

		elif isinstance(i, OprLoadLink):
			# assert(False)
			var = self.encodeElement(i.var)
			loc = self.encodeElement(i.loc)
			encodeOp = self.new_read(var, loc, pid)
			self.info['saveRead'] = encodeOp
		elif isinstance(i, OprStoreCond):
			# assert(False)
			var = self.encodeElement(i.var)
			loc = self.encodeElement(i.loc)
			exp = self.encodeElement(i.exp) 
			prevRead = self.info['saveRead']
			wprev, w2 = Consts('wprev w2', Event) 	# cannot specific to write events in this line...
			rf = Function('rf', Event, Event, BoolSort())
			fr = Function('fr', Event, Event, BoolSort())
			co = Function('co', Event, Event, BoolSort())

			w = self.new_write(loc, exp, pid)
			r = Const('r', Event)

			if prevRead != None and eq(prevRead.target, loc):
				self.info['CS'] += [Or(
						# success ?
						And([ ForAll(wprev,
								Implies(And(rf(wprev, prevRead), Distinct(wprev, w)), 
									# this write follow co immediately
									And(
										ForAll(w2,
											Implies(And(co(wprev, w2), Distinct(w, w2)),
												And(co(wprev, w), co(w, w2))
											)
										),
										co(wprev, w)
									)
								)
							   ),
							  var == 0]),
						# arbitrary fail
						And([var == 1,
							ForAll(w2, 
								And(
									Not(co(w2, w)),
									Not(co(w, w2))
									)
								),
							ForAll(r,Not(rf(w, r)))
							])
						)]
				if not('scWrites' in self.info): 
					self.info['scWrites'] = []
				self.info['scWrites'] += [w]
				encodeOp = w
			else:
				# do nothing and result is 0 
				self.info['CS'] += [var == 1]

			# prevRead is a pair of this write ?
			# if so(same loc)-> add fact....
			# 	   add this write as a special write
			#      write can arbitrary fail or not same beacuase of implementation ...
			# if not -> write not appear and return 0(fail)
			# 	do not add write, return None...

			# fact CS 
			# wprev -rf-> (r_ll of this write)
			# exists w'. wprev -co-> w' /\ w' -co-> w
			#   this w has no effect... or not exists ?
			#    - not exists =>   
		elif isinstance(i, RmwStm):
			assert(False)
		else:
			assert(False)

		return encodeOp

	def encodeSpecific(self):

		# realize po

		po = Function('po', Event, Event, BoolSort())
		for x in self.info['Ev']:
			for y in self.info['Ev']:
				self.info['CS'] += [ po(x,y) if (x.eid,y.eid) in self.info['poS'] else Not(po(x,y)) ]

		# initial_location
		# for L in self.info['Loc'].values():
		# 	self.info['CS'] += [initial_value(L) == 0]
		WriteInit = [self.new_write(v, 0, 0) for v in self.info['Loc'].values()]
		self.info['Ev'] += WriteInit
		# print self.info['PS']
		(co, co_axiom) = conflict_order(self.info['Ev'], self.info['scWrites'] if ('scWrites' in self.info) else [])
		(rf, rf_axiom) = read_from(self.info['Ev'])
		(fr, fr_axiom) = from_read(rf, co)


		(iico, iicoSet, iico_axiom) = iico_relation(self.info['iico'], self.info['Ev'])
		#  - rf-reg : W-reg x R-reg relation
		(rf_reg, rf_regSet, rf_reg_axiom) = rf_reg_relation(self.info['Ev'])

		self.info['rel_po'] = po
		self.info['rel_co'] = co
		self.info['rel_rf'] = rf 
		self.info['rel_fr'] = fr 
		self.info['rel_iico'] = iico 
		self.info['rel_rf_reg'] = rf_reg

		# underlying axioms
		model_axiom = self.model_axioms()
		# print
		# return False
		# print self.info['Loc'].values()
		return And(And(self.info['CS'] + [model_axiom, co_axiom, rf_axiom, fr_axiom, iico_axiom, rf_reg_axiom]),Not(And(self.info['PS'])))


	def model_axioms(self):
		if self.model == 'SC':
			return sc_constraints(self.info['rel_po'], self.info['rel_rf'], self.info['rel_fr'], self.info['rel_co'], self.info['Ev'], self.info['RMW'])
		elif self.model == 'PSO':
			return PSO_model(self.info)
		return []
