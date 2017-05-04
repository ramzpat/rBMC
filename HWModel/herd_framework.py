# herd_framework

from z3 import *

# Abstract model def 
Proc = 		IntSort()			 			# Processor
# Loc = 		DeclareSort('Loc')				# Location
Instr = 	DeclareSort('Instr')			# Instruction 
# Val = 		IntSort()						# Value in the systems
# Reg =		IntSort()						# Registers

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

def is_reg(e):
	return eq(e.decl(), Reg)
def is_intVal(e):
	return eq(e.decl(), Val.int)



# Event =		DeclareSort('Event')

# ReadOp = 	DeclareSort('ReadOp')			# Read access 	*A kind of memory operation(MemOp)
# WriteOp = 	DeclareSort('WriteOp')			# Write access 	*A kind of memory operation(MemOp) 
# FenceOp = 	DeclareSort('FenceOp')			# Fence operator 
# ReadReg = 	DeclareSort('ReadReg')
# WriteReg = 	DeclareSort('WriteReg')

Event =		Datatype('Event')
Event.declare('undefined')
Event.declare('event', 		('eid', IntSort()), ('pid', Proc))
Event.declare('read',  		('eid', IntSort()), ('loc', Loc), ('dest', IntSort()), ('pid', Proc))
Event.declare('write', 		('eid', IntSort()), ('loc', Loc), ('val', IntSort()), ('pid', Proc))
Event.declare('fence', 		('eid', IntSort()), ('ftype', IntSort()))
Event.declare('read_reg', 	('eid', IntSort()), ('reg', Val), ('dest', IntSort()), ('pid', Proc) )
Event.declare('write_reg', 	('eid', IntSort()), ('reg', Val), ('val', IntSort()), ('pid', Proc))
Event.declare('branch', ('eid', IntSort()), ('pid', Proc))
Event = Event.create()
ConstEvent = Event.event
ReadOp = Event.read
WriteOp = Event.write
WriteReg = Event.write_reg
ReadReg = Event.read_reg
Branch = Event.branch

eidCnt = 0


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

id_loc = 0
def new_loc(name):
	global global_axioms
	global id_loc

	loc = Const(name, Loc)
	global_axioms += [idLoc(loc) == id_loc]
	id_loc += 1
	return loc

def new_read(name, location, val, pid = 0):
	global eidCnt
	if is_reg(location):
		read = ReadReg(eidCnt, location, val, pid) #Const(name, ReadReg)
	else:
		read = ReadOp(eidCnt, location, val, pid) #Const(name, ReadOp)
	eidCnt += 1
	read.target = location
	read.val = val
	read.pid = pid
	return read
	

def new_write(name, location, val, pid = 0):
	global eidCnt
	# if is_const(val):
	# 	v = val
	# else:
	# v = Val.int(val) if type(val) == int else val
	v = val
	if is_reg(location):
		write = WriteReg(eidCnt, location, v, pid ) #Const(name, WriteReg)	
		
	else: 
		write = WriteOp(eidCnt, location, v, pid) #Const(name, WriteOp)
	eidCnt += 1	
	write.target = location
	write.val = v 
	write.pid = pid
	return write


# Untilized function
def getSymbolic((rw, loc, proc)):
	return rw

def getWrites(RW):
	return [w for w in RW if (getSymbolic(w).sort() if type(w) == tuple else w.sort()) == WriteOp]

def getReads(RW):
	return [r for r in RW if (getSymbolic(r).sort() if type(r) == tuple else r.sort()) == ReadOp]


def restrict(e, sets = [], Dom = None):
	return Or([e == i for i in sets ])

# Relation defifnition
def relation(r_name, Dom, Set = []):
	e = []
	r = Function(r_name, Dom, Dom, BoolSort())
	x = Const('x', Dom)
	y = Const('y', Dom)

	return (r, [ForAll([x,y], r(x,y) ==  Or([And(x == Dom.cast(i), y == Dom.cast(j)) for (i,j) in Set]))])

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

# Relation with trasitive and irreflexive
def program_order(s, PoSet = []):
	po = Function('po', Event, Event, BoolSort())
	s.register_relation(po)

	x, y, z = Consts('x y z', Event)
	s.declare_var(x, y, z)	
	for (i,j) in poS:
		s.add(po(i, j)) 
	s.rule(po(x,z), [po(x,y), po(y,z)])
	s.add(Not(po(x,x)))
	s.add(Implies(po(x,y), Not(po(y,x))))

	return (s, po)


# Execution (E, po, rf, co)
# co - coherrence 
def conflict_order(s, Ev = []):
	co = Function('co', Event, Event, BoolSort())
	s.register_relation(co)

	for e1 in Ev:
		for e2 in Ev:
			# if eq(e1.target, e2.target) and not(eq(e1.arg(0),e2.arg(0))):
			# 	print str((e1,e2)) + ': ' + str(eq(e1.target, e2.target))
			s.add(
				co(e1, e2) == (
					And(Distinct(e1, e2),
						Not(co(e2, e1),
						e1.target == e2.target
						)
					if not(eq(e1.arg(0),e2.arg(0))) and isWrite(e1) and isWrite(e2) else False
					)
				),
			)
	return (s, co)

# rf - one to many
def read_from(s, Ev = []):
	def candidate_writes(r, Ev = []):
		write =[w for w in Ev if isWrite(w) and eq(w.target, r.target) ]
		# print locB
		# candidate_w = [ (w,locA,pA) for (w,locA,pA) in write if (eq(locA, locB))]
		return write

	# rf : W x R relation
	e = Const('e', Event)
	rf = Function('rf', Event, Event, BoolSort())
	s.register_relation(rf)
	for e1 in Ev:
		if isRead(e1):
			# print e1
			# print candidate_writes(e1, Ev)
			cWrite = candidate_writes(e1, Ev)
			s.add(Or([rf(w, e1) for w in cWrite ]))
			# rf-val
			s.add(And([
				Implies(rf(w, e1), w.val == e1.val)
				for w in cWrite
				])
			)
			# rf-loc
		else:
			s.add(ForAll(e, Not(rf(e,e1))))
	return (s, rf)

def iico_relation(s, S = []):
	# iico = Function('iico', Event, Event, BoolSort())
	# s.register_relation(iico)

	# e1, e2 = Consts('e1 e2', Event)
	# s.add(
	# 	iico(e1, e2) == And(

	# 		)
	# 	)
	(iico, axiom) = relation('iico', Event, S)
	s.register_relation(iico)
	s.add(axiom)
	return (s, iico)

def rf_reg_relation(s, Ev = []):
	def candidate_writes(r, Ev = []):
		write =[w for w in Ev if isWriteReg(w) and eq(w.target, r.target) ]
		return write

	# rf : W-reg x R-reg relation
	e = Const('e', Event)
	rf_reg = Function('rf-reg', Event, Event, BoolSort())
	s.register_relation(rf_reg)
	for e1 in Ev:
		if isReadReg(e1):
			cWrite = candidate_writes(e1, Ev)
			s.add(Or([rf_reg(w, e1) for w in cWrite ]))
			# rf-val
			s.add(And([
				Implies(rf_reg(w, e1), w.val == e1.val)
				for w in cWrite
				])
			)
			# rf-loc
		else:
			s.add(ForAll(e, Not(rf_reg(e,e1))))
	return (s, rf_reg)

# dd-reg = (rf-reg U iico)+
def dd_reg_relation(s, rf_reg, iico):
	dd_reg = Function('dd_reg', Event, Event, BoolSort())
	s.register_relation(dd_reg)
	e1, e2, e3 = Consts('e1 e2 e3', Event)
	s.declare_var(e1, e2, e3)
	s.rule(dd_reg(e1, e2), rf_reg(e1, e2)) 
	s.rule(dd_reg(e1, e2), iico(e1, e2))
	s.rule(dd_reg(e1, e3), [dd_reg(e1, e2), dd_reg(e2, e3)])
	s.vars = []
	return (s, dd_reg)

# addr dependency = dd-reg ^ RM
def addr_dependency(s, dd_reg, Ev = []):
	addr_dep = Function('addr_dep',Event, Event, BoolSort())
	s.register_relation(addr_dep)

	# e1, e2, e3 = Consts('e1 e2 e3', Event)
	# s.declare_var(e1, e2, e3)
	for e1 in Ev:
		for e2 in Ev:
			if isRead(e1) and isRW(e2):
				s.add(addr_dep(e1, e2) == And(dd_reg(e1, e2)) )
			else:
				s.add(Not(addr_dep(e1, e2)))
	# s.vars = []
	return (s, addr_dep)

# data dep = dd-reg ^ RW
def data_dependency(s, dd_reg, Ev = []):
	data_dep = Function('data_dep', Event, Event, BoolSort())
	s.register_relation(data_dep)

	for e1 in Ev:
		for e2 in Ev:
			if isRead(e1) and isWrite(e2):
				s.add(data_dep(e1, e2) == And(dd_reg(e1, e2)))
			else:
				s.add(Not(data_dep(e1, e2)))
	return (s, data_dep)

# ctrl = (dd_reg ^ RB);po
def ctrl_dependency(s, dd_reg, po, Ev = []):
	ctrl = Function('ctrl', Event, Event, BoolSort())
	s.register_relation(ctrl)	

	e1, e2, b = Consts('e1 e2 b', Event)
	s.declare_var(e1, e2, b)
	s.rule(ctrl(e1, e2), [ isRead(e1), isBranch(b), dd_reg(e1,b), po(b, e2) ])
	s.vars = []
	return (s, ctrl)

# ctrl+cfence = (dd_reg ^ RB);cfence
def ctrl_cfence_dependency(s, dd_reg, cfence, Ev = []):
	ctrl_cfence = Function('ctrl_cfence', Event, Event, BoolSort())
	s.register_relation(ctrl)	

	e1, e2, b = Consts('e1 e2 b', Event)
	s.declare_var(e1, e2, b)
	s.rule(ctrl(e1, e2), [ isRead(e1), isBranch(b), dd_reg(e1,b), cfence(b, e2) ])
	s.vars = []
	return (s, ctrl_cfence)

# fr - fromread (fixed point) 
def from_read(s, rf, co):
	fr = Function('fr', Event, Event, BoolSort())
	s.register_relation(fr)

	e1, e2, e3 = Consts('e1 e2 e3', Event)
	s.declare_var(e1,e2,e3)
	# invrf = rf^-1
	# fr = (invrf ; co) \ id
	s.rule(fr(e1,e3), [rf(e2, e1), co(e2, e3), e1 != e3])
	s.vars = []
	return (s, fr)

# # fr - fromread
# def from_read(RW = []):
# 	fr = Function('fr', ReadOp, WriteOp, BoolSort())

# 	# fr.domain = (lambda i: ReadOp if i == 0 else WriteOp)

# 	# fr = { (r, w1) | exists w0. rf(w0,r) and co(w0, w1) } 

# 	writes = getWrites(RW)
# 	reads = getReads(RW)

# 	def getConflictRead((w, locW, xW), RW):
# 		return [(r, locR, xR) for (r, locR, xR) in getReads(RW) if eq(locR, locW) ]

# 	# print getConflictRead(writes[2], RW)

# 	w0 = Const('w0', WriteOp)

# 	# print [
# 	# 	(locW, locR)
# 	# 	# if eq(locW, locR)
# 	# 	# else Not(fr(r,w))
# 	# 	for (w, locW, vW) in writes for (r, locR, vR) in reads
# 	# ]

# 	axiom = [
# 		# fr(getSymbolic(r), getSymbolic(w)) == Exists([w0], And(restrict(w0, writes, WriteOp),rf(w0, getSymbolic(r)), co(w0,getSymbolic(w))))
# 		# for w in writes for r in getConflictRead(w, RW)
# 		fr(r, w) == Exists(w0, And( restrict(w0, writes, WriteOp), rf(w0, r), co(w0, w) ))
# 		if (eq(locW, locR))
# 		else Not(fr(r,w))
# 		for (w, locW, vW) in writes for (r, locR, vR) in reads
# 	]
# 	return (fr, axiom)

# comm - Communucation = co U rf U fr
def comm(RW = []):
	comm = Function('comm', Event, Event, BoolSort())
	comm.domain = (lambda i: Event)
	axiom = [
	(comm(x, y) == 
		simplify(Or( [
			co(x,y) if isWrite((x, locX, vX)) and isWrite((y, locY, vY)) else False, 
			rf(x,y) if isWrite((x, locX, vX)) and isRead((y, locY, vY)) else False, 
			fr(x,y) if isRead((x, locX, vX)) and isWrite((y, locY, vY)) else False, 
			] 
			)) if ( x.sort() != y.sort() or (x, locX, vX) != (y, locY, vY))
		else Not(comm(x,y)))
		for (x, locX, vX) in RW for (y, locY, vY) in RW  
	]
	return (comm, axiom)

# po-loc = { (x,y) in po and addr(x) = addr(y)}
def po_loc(RW = []):
	po_loc = Function('po-loc', Event, Event, BoolSort())
	po_loc.domain = (lambda i: Event)
	axiom = [
		(po_loc(x,y) == po(x,y)
		if (( x.sort() != y.sort() or (x, locX, vX) != (y, locY, vY))) and eq(locX,locY)
		else Not(po_loc(x,y))
		)
		for (x, locX, vX) in RW for (y, locY, vY) in RW  
	]
	return (po_loc, axiom)

# SC PER LOCATION - acyclic(po-loc U comm)
def SCPerLoc(RW = []):
	sc_per_loc = Function('sc_per_loc', Event, Event, BoolSort())
	sc_per_loc.domain = (lambda i: Event)
	union_sc = Function('union_poLoc_comm', Event, Event, BoolSort())

	e = Const('e', Event)

	axiom = [
		sc_per_loc(x, y) == Or([
				po_loc(x,y),
				comm(x,y), 
				# transitive
				Exists([e], And([restrict(e, RW, Event), sc_per_loc(x,e), sc_per_loc(e,y) ]) )
			]) 
		# if not(eq(x,y))
		# else Not(sc_per_loc(x, y))
		for (x, locX, vX) in RW for (y, locY, vY) in RW 
	]
	# acyclic
	axiom += [
		ForAll(e, Not(sc_per_loc(e,e)))
	]
	# print axiom 

	return (sc_per_loc, axiom)
	# comm
	# [(Ry1, Wy0), (Rx1, Wx0), (Wx1, Rx1), (Wx1, Wx0), (Wy1, Ry1), (Wy1, Wy0)]
	# [                        (Wx1, Rx1), (Wy1, Wy0), (Wx0, Wx1), (Wy0, Ry1)]

ppo = Function('ppo', Event, Event, BoolSort())
ppo.domain = (lambda i: Event)

fences = Function('fence', Event, Event, BoolSort())
fences.domain = (lambda i: Event)

# rfe = Function('rfe', WriteOp, ReadOp, BoolSort())
def rfe_axiom(Ev = []):
	writes = getWrites(Ev)
	reads = getReads(Ev)
	return [
		rfe(w,r) == And(rf(w,r), proc(w) != proc(r))
		for (w, locW, vW) in writes for (r, locR, vR) in reads 
	]

hb = Function('hb', Event, Event, BoolSort())
hb.domain = (lambda i: Event)
def hb_axiom(Ev = []):
	global hb
	return [
		hb(x,y) == simplify(Or([
			ppo(x,y), fences(x,y),
			( rfe(x,y) if (x.sort() == WriteOp) and (y.sort() == ReadOp) else False )
			]
			))
		for (x, locX, v1) in Ev for (y, locY, v2) in Ev
	]

noThinAir = Function('no_thin_air', Event, Event, BoolSort())
noThinAir.domain = (lambda i: Event)
def no_thin_air_axiom(Ev = []):
	e = Const('e', Event)
	axiom = [
		noThinAir(x,y) == Or(
				hb(x,y), 
				Exists(e, And(restrict(e, Ev, Event), noThinAir(x, e), noThinAir(e,y)))
			)
		# if not(eq(x,y))
		# else Not(noThinAir(x,y))
		for (x, locX, v1) in Ev for (y, locY, v2) in Ev
	] 
	axiom += [ # acyclic
		ForAll(e, Not(noThinAir(e,e)))
	]
	return axiom
# observ = irreflexive(fre;prop;hb*)
def observation(Ev = []):
	fre = Function('fre', ReadOp, WriteOp, BoolSort())
	fre.domain = (lambda i: ReadOp if i == 0 else WriteOp)

	# hb* : reflextive transitive
	hbRT = Function('hb*', Event, Event, BoolSort())
	hbRT.domain = (lambda i: Event)

	# (fre;prop)
	prop = Function('prop', Event, Event, BoolSort())
	prop.domain = (lambda i: Event)
	freProp = Function('fre;prop', ReadOp, Event, BoolSort())
	freProp.domain = (lambda i: ReadOp if i == 0 else Event)

	# irreflexive(fre;prop;hb*)
	frePropHbST = Function('fre;prop;hb*', ReadOp, Event, BoolSort())
	frePropHbST.domain = (lambda i: ReadOp if i == 0 else Event)

	writes = getWrites(Ev)
	reads = getReads(Ev)

	e = Const('e', Event)
	w = Const('w', WriteOp)

	axiom = [
		# fr
		fre(x,y) == And(fr(x,y), proc(x) != proc(y))
		for (x, locX, v1) in reads for (y, locY, v2) in writes
	]
	axiom += [
		# hb*
		hbRT(x,y) == Or([
				hb(x,y), 
				Exists(e, And(restrict(e, Ev, Event), hb(x,e), hb(e,y)))
			])
		for (x, locX, v1) in Ev for (y, locY, v2) in Ev
	]
	axiom += [
		And(
		# (fre;prop)
		freProp(x,y) == Exists(w, And(restrict(w, writes, WriteOp), fre(x,w), prop(w, y))),
		# (fre;prop;hb*)
		frePropHbST(x,y) == And( Exists(e, And(restrict(e, Ev, Event), freProp(x,e), hbRT(e,y))) )
		)
		for (x, locX, v1) in reads for (y, locY, v2) in Ev
	]
	axiom += [
		# irreflexive(fre;prop;hb*)
		ForAll([w], Not(frePropHbST(w,w)))
	]

	return axiom

# propagation = acyclic(co U prop)
def propagation(Ev = []):
	prop = Function('prop', Event, Event, BoolSort())
	prop.domain = (lambda i: Event)

	co = Function('co', WriteOp, WriteOp, BoolSort())
	co.domain = (lambda i: WriteOp)

	prog = Function('propagation', Event, Event, BoolSort())
	prog.domain = (lambda i: Event)

	e = Const('e', Event)

	axiom = [
		prog(x,y) == simplify(Or([
			co(x,y) if x.sort() == WriteOp and y.sort() == WriteOp else False,
			prop(x,y),
			Exists(e, And(restrict(e, Ev, Event), prog(x,e), prog(e,y)))
			])) 
		# if not(eq(x,y)) else Not(prog(x,y))
		for (x, locX, v1) in Ev for (y, locY, v2) in Ev
	]
	axiom += [
		# acyclic
		ForAll(e, Not(prog(e,e)))
	]
	return axiom


# arch = (ppo, fences, prop)
def sc_constraints(RW = [], Fence = []):
	# ppo : po
	# ffence : empty
	# lwfence : empty 
	# fences = ffence U lwfence
	# prop = ppo U fences U rf U fr
	ppo = Function('ppo', Event, Event, BoolSort())
	ffence = Function('ffence', Event, Event, BoolSort())
	lwfence = Function('lwfence', Event, Event, BoolSort())
	fences = Function('fence', Event, Event, BoolSort())
	prop = Function('prop', Event, Event, BoolSort())

	ppo.domain = (lambda i: Event)
	ffence.domain = (lambda i: Event)
	lwfence.domain = (lambda i: Event)
	fences.domain = (lambda i: Event)
	prop.domain = (lambda i: Event)

	axiom = [
		And([	ppo(x, y) == po(x,y),
				Not(ffence(x,y)),
				Not(lwfence(x,y)),
				fences(x,y) == Or(ffence(x,y), lwfence(x,y)),
				prop(x,y) == simplify(Or([
					ppo(x,y), 
					fences(x,y), 
					rf(x,y) if x.sort() == WriteOp and y.sort() == ReadOp else False, 
					fr(x,y) if x.sort() == ReadOp and y.sort() == WriteOp else False
					]))
			])
		for (x, locX, v1) in RW for (y, locY, v2) in RW
	]
	return axiom

def tso_constraints(RW = [], Fence = []):
	# ppo = po\WR
	# ffence = mfence
	# lwfence = empty
	# fences = ffence U lwfence
	# prop = ppo U fences U rfe U fr

	ppo = Function('ppo', Event, Event, BoolSort())
	# ffence = Function('ffence', Event, Event, BoolSort())
	(ffence, axiom_fence) = relation('ffence', Event, Fence)
	lwfence = Function('lwfence', Event, Event, BoolSort())
	fences = Function('fence', Event, Event, BoolSort())
	prop = Function('prop', Event, Event, BoolSort())

	ppo.domain = (lambda i: Event)
	ffence.domain = (lambda i: Event)
	lwfence.domain = (lambda i: Event)
	fences.domain = (lambda i: Event)
	prop.domain = (lambda i: Event)

	axiom = axiom_fence
	axiom += [
		And([	
				# ppo = po\WR
				# ppo(x, y) == po(x,y),
				ppo(x, y) == (po(x,y) if x.sort() != WriteOp or y.sort() != ReadOp else False), 
				Not(lwfence(x,y)),
				fences(x,y) == Or(ffence(x,y), lwfence(x,y)),
				# prop = ppo U fences U rfe U fr
				prop(x,y) == simplify(Or([
					ppo(x,y), 
					fences(x,y), 
					rfe(x,y) if x.sort() == WriteOp and y.sort() == ReadOp else False, 
					fr(x,y) if x.sort() == ReadOp and y.sort() == WriteOp else False
					]))
			])
		for (x, locX, v1) in RW for (y, locY, v2) in RW
	]
	return axiom

def power_constraints(Ev = []):
	# ffence = sync 
	# lwfence = lwsync \ WR

	# Propogation order for Power
	# 

	axioms = []
	return axioms

def pso_constraints(RW = [], Fence = []):
	# ppo = po\(WR U WW)
	# ffence = mfence
	# lwfence = empty
	# fences = ffence U lwfence
	# prop = ppo U fences U rfe U fr

	ppo = Function('ppo', Event, Event, BoolSort())
	# ffence = Function('ffence', Event, Event, BoolSort())
	(ffence, axiom_fence) = relation('ffence', Event, Fence)
	lwfence = Function('lwfence', Event, Event, BoolSort())
	fences = Function('fence', Event, Event, BoolSort())
	prop = Function('prop', Event, Event, BoolSort())

	ppo.domain = (lambda i: Event)
	ffence.domain = (lambda i: Event)
	lwfence.domain = (lambda i: Event)
	fences.domain = (lambda i: Event)
	prop.domain = (lambda i: Event)

	axiom = axiom_fence
	axiom += [
		And([	
				# ppo = po\ ( WR U WW ) = po ^ ( RR U RW )
				ppo(x, y) == (po(x,y) if x.sort() != WriteOp else False), 
				Not(lwfence(x,y)),
				fences(x,y) == Or(ffence(x,y), lwfence(x,y)),
				# prop = ppo U fences U rfe U fr
				prop(x,y) == simplify(Or([
					ppo(x,y), 
					fences(x,y), 
					rfe(x,y) if x.sort() == WriteOp and y.sort() == ReadOp else False, 
					fr(x,y) if x.sort() == ReadOp and y.sort() == WriteOp else False
					]))
			])
		for (x, locX, v1) in RW for (y, locY, v2) in RW
	]
	return axiom

# constraining 
def acyclic(s, *rel):
	print str(rel)
	trans = Function('acyclic' + str(rel), Event, Event, BoolSort())
	s.register_relation(trans)
	e1, e2, e3 = Consts('e1 e2 e3', Event)
	s.declare_var(e1, e2, e3)
	for r in rel:
		s.rule(trans(e1, e2), r(e1, e2))
	s.rule(trans(e1, e2), [trans(e1, e3), trans(e3, e2)])
	s.add(Not(trans(e1,e1)))
	s.vars = []
	return trans

if __name__ == '__main__':
	# try ARM models

	# s = Solver()
	s = Fixedpoint()
	s.set(engine='pdr')

	# x, y = Consts('x y', Loc)

	addrX, addrY = Ints('addrX addrY')
	x = InitLoc(addrX)
	y = InitLoc(addrY)
	s.add(Distinct(x,y))
	# s.add(ForAll([x,y], (addrLoc(x) == addrLoc(y)) == (x == y) ))

	
	# s.add(addrLoc(x) == addrX, addrLoc(y) == addrY)
	
	# print x
	# inital value
	Wx0 = new_write('Wx0', x, 0)
	Wy0 = new_write('Wy0', y, 0)

	pid1, pid2 = Consts('pid1 pid2', Proc)
	s.add(Distinct(pid1, pid2))
	
	# P1
	# r1, r2, r3 = Consts('r1 r2 r3', Reg)
	r1 = Reg(0)
	r2 = Reg(1)
	r3 = Reg(2)

	# mov r1, #1
	Wr1 = new_write('Wr1_0', r1, 1, 1)
	# mov r2, x
	Wr2 = new_write('Wr2_0', r2, addrX, 1)
	# mov r3, y
	Wr3 = new_write('Wr3_0', r3, addrY, 1)

	# str r1, [r2/x]
	tempAddr1 = Int('tempAddr1')
	Rr2 = new_read('Rr2_0', r2, tempAddr1, 1)
	loc1 = InitLoc(addrX)
	# loc1 = Const('loc1', Loc)
	# s.add(addrLoc(loc1) == TempAddr)

	Vr1_0 = Int('Temp1')
	Rr1_0 = new_read('Rr1_0', r1, Vr1_0, 1)
	
	Wx1 = new_write('Wx1_0', loc1, Vr1_0, 1)

	# str r1, [r3/y]
	TempAddr2 = Int('Temp3')
	Rr3 = new_read('Rr3_0', r3, TempAddr2, 1)
	loc2 = InitLoc(addrY)
	# loc2 = Const('loc2', Loc)
	Vr1_1 = Int('Temp4')
	Rr1_1 = new_read('Rr1_1', r1, Vr1_1, 1)
	
	# s.add(addrLoc(loc2) == TempAddr2)
	Wy1 = new_write('Wy1_0', loc2, Vr1_1, 1)

	Ev1 = [Wx0, Wy0, Wr1, Wr2, Wr3, Rr1_0, Rr2, Rr3, Rr1_1, Wx1, Wy1]
	# print [ev.sort() for ev in Ev1 if isWriteReg(ev) ]

	# P2 
	r4, r5, r6, r7 = Reg(3), Reg(4), Reg(5), Reg(6)


	# mov r4, x
	Wr4 = new_write('Wr4', r4, addrX, 2)
	# mov r5, y
	Wr5 = new_write('Wr5', r5, addrY, 2)
	# ldr r6, [r5]
	Vr5 = Int('Temp5')
	Rr5 = new_read('Rr5', r5, Vr5, 2)
	loc3 = InitLoc(addrY)
	# loc3 = Const('loc3', Loc)
	# s.add(addrLoc(loc3) == Int('Vr5'))
	Vloc3 = Int('Temp6')
	Rvr5 = new_read('Rvr5', loc3, Vloc3, 2) 
	Wr6 = new_write('Wr6', r6, Vloc3, 2)
	# ldr r7, [r4]
	Vr4 = Int('Temp7')
	Rr4 = new_read('Rr4', r4, Vr4, 2)
	# loc4 = Const('loc4', Loc)
	# s.add(addrLoc(loc4) == Int('Vr4'))
	loc4 = InitLoc(addrX)
	Vloc4 = Int('Temp8')
	Rvr4 = new_read('Rvr4', loc4, Vloc4, 2) 
	Wr7 = new_write('Wr7', r7, (Vloc4), 2)
	
	Ev2 = [Wr4, Wr5, Rr5, Rvr5, Wr6, Rr4, Rvr4, Wr7]
	# print [ev[0] for ev in Ev2 if ev[0].sort() == ReadOp or ev[0].sort() == WriteOp ]

	# manual po
	poS = []
	# po for P1
	poS += [(Wx0, Wy0), (Wy0, Wr1), (Wr1, Wr2), (Wr2, Wr3)]
	poS += [(Wr3, Rr2), (Wr3, Rr1_0), (Rr2, Wx1), (Rr1_0, Wx1)]
	poS += [(Wx1, Rr3), (Wx1, Rr1_1), (Rr3, Wy1), (Rr1_1, Wy1)]
	# po for P2 
	poS += [(Wy0, Wr4), (Wr4, Wr5), (Wr5, Rr5), (Rr5, Rvr5) ,(Rvr5, Wr6), (Wr6, Rr4), (Rr4, Rvr4), (Rvr4, Wr7)]

	# manual iico
	iicoS = []
	# iico for P1 
	iicoS += [(Rr2, Wx1), (Rr1_0, Wx1), (Rr3, Wy1), (Rr1_1, Wy1)]
	# iico for P2
	iicoS += [(Rr5, Rvr5), (Rvr5, Wr6), (Rr4, Rvr4), (Rvr4, Wr7)]
	
	# distinct events
	s.add(Distinct([ e for e in Ev1 + Ev2 ]))

	# generate axioms for:
	#  - po : E x E relation
	(s, po) = program_order(s, poS)
	#  - co : W x W relation
	(s, co) = conflict_order(s, Ev1 + Ev2)
	#  - rf : W x R relation
	(s, rf) = read_from(s, Ev1 + Ev2)
	

	# Instruction semantics level
	#  - iico : E x E relation
	(s, iico) = iico_relation(s, iicoS)
	#  - rf-reg : W-reg x R-reg relation
	(s, rf_reg) = rf_reg_relation(s, Ev1 + Ev2)

	cfence = Function('cfence', Event, Event, BoolSort())
	s.register_relation(cfence)

	#  -- dependency relation
	#  - dd_reg
	(s, dd_reg) = dd_reg_relation(s, rf_reg, iico)
	(s, addr_dep) = addr_dependency(s, dd_reg, Ev1 + Ev2)
	(s, data_dep) = data_dependency(s, dd_reg, Ev1 + Ev2)
	(s, ctrl) = ctrl_dependency(s, dd_reg, po, Ev1 + Ev2)
	(s, ctrl_cfence) = ctrl_cfence_dependency(s, dd_reg, cfence, Ev1 + Ev2)
	
	(s, fr) = from_read(s, rf, co)

	fre = Function('fre', Event, Event, BoolSort())
	fri = Function('fri', Event, Event, BoolSort())
	s.register_relation(fre, fri)

	for e1 in Ev1 + Ev2:
		for e2 in Ev1 + Ev2:
			s.add(fre(e1, e2) == And(fr(e1,e2), Not(e1.pid == e2.pid)))
			s.add(fri(e1, e2) == And(fr(e1,e2), (e1.pid == e2.pid)))

	# SC ----------
	# (* Atomic *)
	# empty rmw & (fre;coe) as atom
	# s.add(Not( ) )
	# (* Sequential consistency *)
	# acyclic po | fr | rf | co as sc
	print (acyclic(s, po, fr, rf, co))


	# check prob
	# print Wx0
	# print Wx1
	# s.add(rf(Wx0, Rvr4))
	# s.add(rf(Wx1, Rvr4))
	
	# s.add(Rvr5.val == 1)
	# s.add(Rvr4.val == 0)
	# print Wx0.val
	# s.add(co(Wx0, Wx1))
	# s.add(co(Wy0, Wy1))
	# s.add(rf(Wy1))

	# s.add(po(Rvr5, Rvr4))
	s.add(po(Rvr4, Rvr5))
	print poS
	print Rvr5
	print Rvr4 
	print s.query()



if __name__ == '__main2__':
	x, y, z = Consts('a b c', Event)
	i, j = Consts('i j', Event)
	# (po_r, axioms1) = relation('po_r',Event, [(x,y), (y,z)])
	# print acyclic(po_r)

	# Message passing 
	# Reads 
	# Ry1, Rx1
	Ry1 = new_read('Ry1', 'y', 'y1', 2)
	Rx1 = new_read('Rx1', 'x', 'x1', 2)
	# Writes
	# Wx1, Ry1
	Wx1 = new_write('Wx1', 'x', 1, 1)
	Wy1 = new_write('Wy1', 'y', 1, 1)
	# initialValue
	Wx0 = new_write('Wx0', 'x', 0, 0)
	Wy0 = new_write('Wy0', 'y', 0, 0)

	x = new_loc('x')
	y = new_loc('y')

	PoSet = [(Wx0, Wx1),(Wy0, Wx1), (Wx1,Wy1), (Ry1,Rx1)]
	RW_S = [Ry1, Rx1, Wx1, Wy1, Wx0, Wy0]

	# execution
	(po, axiom_po) = program_order(PoSet, RW_S)
	(co, axiom_co) = conflict_order(RW_S)
	(rf, axiom_rf) = read_from(RW_S)

	# SC per location
	(fr, axiom_fr) = from_read(RW_S)
	(comm, axiom_comm) = comm(RW_S)
	(po_loc, axiom_po_loc) = po_loc(RW_S)
	(sc_per_loc, axiom_sc) = SCPerLoc(RW_S)

	# No thin air
	axiom_rfe = rfe_axiom(RW_S)
	axiom_hb = hb_axiom(RW_S)
	axiom_noThinAir = no_thin_air_axiom(RW_S)

	# Observation
	axiom_ob = observation(RW_S)
	fre = Function('fre', ReadOp, WriteOp, BoolSort())
	hbST = Function('hb*', Event, Event, BoolSort())
	hbST.domain = (lambda i:Event)
	freProp = Function('fre;prop', ReadOp, Event, BoolSort())
	freProp.domain = (lambda i: ReadOp if i == 0 else Event)
	prop = Function('prop', Event, Event, BoolSort())
	prop.domain = (lambda i: Event)
	# irreflexive(fre;prop;hb*)
	frePropHbST = Function('fre;prop;hb*', ReadOp, Event, BoolSort())
	frePropHbST.domain = (lambda i: ReadOp if i == 0 else Event)

	# propagation
	prog = Function('propagation', Event, Event, BoolSort())
	prog.domain = (lambda i: Event)

	axiom_prog = propagation(RW_S)

	s = Solver()
	s.add(global_axioms
		# execution
		+ axiom_po
		+ axiom_co
		+ axiom_rf
		# SC PER LOC
		+ axiom_fr
		+ axiom_comm
		+ axiom_po_loc
		+ axiom_sc
		# No thin air
		+ axiom_rfe
		+ axiom_hb
		+ axiom_noThinAir
		# Observation
		+ axiom_ob
		# Propogation
		+ axiom_prog
		)

	s.add(pso_constraints(RW_S))

	# print s
	# s.add((po((Wx1),getSymbolic(Wy1))))
	# print ((po(Wx1,Wy1)))
	
	x1 = Int('x1')
	y1 = Int('y1')
	s.add(y1 == 1)
	s.add(x1 == 0)

	u = Const('Wx0', WriteOp)
	v = Const('Wx1', WriteOp)
	# s.add(And(po(u,v), co(v, u)))
	res = s.check()
	print res

	if res == sat and False:
		m = s.model()

		print 'Execution:'
		print 'po = ' + str([
			 (x,y) 
			for (x, locX, vX) in RW_S for (y, locY, vY) in RW_S if is_true(m.evaluate(po(x,y)))
		])
		print 'co = ' + str([
			 (x,y) 
			for (x, locX, vX) in RW_S for (y, locY, vY) in RW_S if isWrite((x, locX, vX)) and isWrite((y, locY, vY)) and is_true(m.evaluate(co(x,y)))
		])
		print 'rf = ' + str([
			 (x,y) 
			for (x, locX, vX) in RW_S for (y, locY, vY) in RW_S if isWrite((x, locX, vX)) and isRead((y, locY, vY)) and is_true(m.evaluate(rf(x,y)))
		])

		print 'SC PER LOCATION:'
		print 'ppo = ' + str([
			(x,y)
			for (x, locX, vX) in RW_S for (y, locY, vY) in RW_S if  is_true(m.evaluate(ppo(x,y))) 
		])
		print 'po-loc = ' + str([
			(x,y)
			for (x, locX, vX) in RW_S for (y, locY, vY) in RW_S if  is_true(m.evaluate(po_loc(x,y))) 
		])
		print 'fr = ' + str([
			(x,y)
			for (x, locX, vX) in RW_S for (y, locY, vY) in RW_S if isRead((x, locX, vX)) and isWrite((y, locY, vY)) and is_true(m.evaluate(fr(x,y)))
		])
		print 'comm = ' + str([
			(x,y)
			for (x, locX, vX) in RW_S for (y, locY, vY) in RW_S if  is_true(m.evaluate(comm(x,y)))
		])
		print 'sc_per_loc = ' + str([
			(x,y)
			for (x, locX, vX) in RW_S for (y, locY, vY) in RW_S if  is_true(m.evaluate(sc_per_loc(x,y)))
		])
		print "No Thin Air:"
		print 'rfe = ' + str([
			(x,y)
			for (x, locX, vX) in RW_S for (y, locY, vY) in RW_S if  isWrite((x, locX, vX)) and isRead((y, locY, vY)) and is_true(m.evaluate(rfe(x,y)))
		])
		print 'hb = ' + str([
			(x,y)
			for (x, locX, vX) in RW_S for (y, locY, vY) in RW_S if  is_true(m.evaluate(hb(x,y)))
		])
		print 'no thin air = ' + str([
			(x,y)
			for (x, locX, vX) in RW_S for (y, locY, vY) in RW_S if  is_true(m.evaluate(noThinAir(x,y)))
		])
		print "Observation:"
		print 'fre = ' + str([
			(x,y)
			for (x, locX, vX) in RW_S for (y, locY, vY) in RW_S if  isRead((x, locX, vX)) and isWrite((y, locY, vY)) and is_true(m.evaluate(fre(x,y)))
		])
		print 'hb* = ' + str([
			(x,y)
			for (x, locX, vX) in RW_S for (y, locY, vY) in RW_S if  is_true(m.evaluate(hbST(x,y)))
		])
		print 'prop = ' + str([
			(x,y)
			for (x, locX, vX) in RW_S for (y, locY, vY) in RW_S if  is_true(m.evaluate(prop(x,y)))
		])
		print 'fre;prop = ' + str([
			(x,y)
			for (x, locX, vX) in RW_S for (y, locY, vY) in RW_S if  isRead((x, locX, vX)) and is_true(m.evaluate(freProp(x,y)))
		])
		print 'irreflexive(fre;prop;hb*) = ' + str([
			(x,y)
			for (x, locX, vX) in RW_S for (y, locY, vY) in RW_S if  isRead((x, locX, vX)) and is_true(m.evaluate(frePropHbST(x,y)))
		])
		# acyclic(co U prop)
		print "Propagation:"
		print 'acyclic(co U po) = ' + str([
			(x,y)
			for (x, locX, vX) in RW_S for (y, locY, vY) in RW_S if  is_true(m.evaluate(prog(x,y)))
		])

		print 'x1 = ' + str(m.evaluate((x1)))
		print 'y1 = ' + str(m.evaluate((y1)))

 # 		print s.model() 


