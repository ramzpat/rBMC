# herd_framework

from z3 import *

# Abstract model def 
Proc = 		IntSort()			 			# Processor
# Loc = 		DeclareSort('Loc')				# Location
Instr = 	DeclareSort('Instr')			# Instruction 
# Val = 		IntSort()						# Value in the systems

Val = Datatype('Val')
Val.declare('undefined')
Val.declare('int', ('val', IntSort()))
Val.declare('register', ('rid', IntSort()))
Val = Val.create()


Loc = Datatype('Loc')
Loc.declare('undefined')
Loc.declare('loc', ('lid', IntSort()))
Loc = Loc.create()

Event =		Datatype('Event')
Event.declare('undefined')
Event.declare('event', ('eid', IntSort()))
Event.declare('read', ('eid', IntSort()), ('loc', Loc), ('dest', Val), ('pid', Proc))
Event.declare('write', ('eid', IntSort()), ('loc', Loc), ('val', Val), ('pid', Proc))
Event.declare('fence', ('eid', IntSort()), ('ftype', IntSort()))
Event = Event.create()
ConstEvent = Event.event


# Allocate new event


id_loc = 0
def new_loc():
	global id_loc

	loc = Loc.loc(id_loc)
	id_loc += 1
	return loc

id_ev = 0
def new_read(name, location, val, pid = 0):
	global id_ev
	
	event = Event.read(id_ev, location, val, pid)
	id_ev += 1
	return event


id_write = 0
def new_write(name, location, val, pid = 0):
	global id_ev
	v = (Val.int(val) if type(val) == int else val)
	event = Event.write(id_ev, location, v, pid)
	id_ev += 1
	return event


# Untilized function
def getSymbolic((rw, loc, proc)):
	return rw

def getWrites(RW):
	return [w for w in RW if (getSymbolic(w).sort() if type(w) == tuple else w.sort()) == WriteOp]

def getReads(RW):
	return [r for r in RW if (getSymbolic(r).sort() if type(r) == tuple else r.sort()) == ReadOp]

def isWrite(e):
	return eq(e.decl(), Event.write)
def isRead(rw):
	return eq(e.decl(), Event.read)
def isFence(f):
	return eq(e.decl(), Event.fence)

def isRW(rw):
	return isRead(rw) or isWrite(rw)

def restrict(e, sets = [], Dom = None):
	return Or([e == Dom.cast(getSymbolic(i)) for i in sets ])

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
# def acyclic(name, r, PoSet = []):
# 	dom = r.domain(0)
# 	x, y = Consts('x y', dom)
# 	(r_trans,axiom) = transitive(name, r, sets)
# 	return (r_trans, axiom + [Not(Exists([x], r_trans(x,x) ))])

# Execution (E, po, rf, co)
# Relation with trasitive and irreflexive
def program_order(fp, PoSet = []):
	po = Function('po', Event, Event, BoolSort())
	fp.register_relation(po)

	x, y, z = Consts('x y z', Event)
	fp.declare_var(x, y, z)	
	for (i,j) in PoSet:
		fp.fact(po(i, j)) 
	fp.rule(po(x,z), [po(x,y), po(y,z)])
	return (fp,po)

# co - coherrence 
def conflict_order(fp, Set = []):
	# co (W,W)
	# co def
	co = Function('co', Event, Event, BoolSort())
	fp.register_relation(co)

	eid1, eid2 = Ints('eid1 eid2')
	loc = Const('loc', Loc)
	r1, r2 = Consts('r1 r2', Val)
	pid1, pid2 = Ints('pid1 pid2')
	write = Event.write
	fp.declare_var(eid1, eid2, loc, r1, r2, pid1, pid2)
	fp.vars = [eid1, eid2, loc, r1, r2, pid1, pid2]
	fp.rule( co(write(eid1, loc, r1, pid1), write(eid2, loc, r2, pid2)), 
			[ Distinct(eid1, eid2) ] )

	x, y = Consts('x y', Event)
	fp.declare_var(x,y)
	fp.vars = [x,y]
	# asymmetric
	fp.add(ForAll([x,y], Implies( co(x,y), Not(co(y,x)) ) ))

	return (fp, co)

# rf - one to many
def read_from(fp, Set = []):

	def conflict_rf(Set = []):
		read = [r for r in Set if getSymbolic(r).sort() == ReadOp]
		write =[w for w in Set if getSymbolic(w).sort() == WriteOp]
		candidate_rf = [ ((w,locA,pA), (r,locB,pB)) for (w,locA, pA) in write for (r,locB,pB) in read if (eq(locA, locB))]
		return candidate_rf
	def candidate_writes((r, locB, pB), Set = []):
		write =[w for w in Set if getSymbolic(w).sort() == WriteOp]
		# print locB
		candidate_w = [ (w,locA,pA) for (w,locA,pA) in write if (eq(locA, locB))]
		return candidate_w

	
	# rf : WR
	rf = Function('rf', Event, Event, BoolSort())
	fp.register_relation(rf)

	# one to many (read can read from only one write)
	x = Const('x', Event)
	y = Const('y', Event)
	fp.vars = []
	fp.declare_var(x,y)
	fp.rule(rf(x,y), [is_write(x), is_read(y)])

	# read = [r for r in Set if getSymbolic(r).sort() == ReadOp]
	# write = [w for w in Set if getSymbolic(w).sort() == WriteOp]
	# candidate_rf = conflict_rf(Set)
	
	return (fp, rf)


# fr - fromread
def from_read(RW = []):
	fr = Function('fr', ReadOp, WriteOp, BoolSort())

	# fr.domain = (lambda i: ReadOp if i == 0 else WriteOp)

	# fr = { (r, w1) | exists w0. rf(w0,r) and co(w0, w1) } 

	writes = getWrites(RW)
	reads = getReads(RW)

	def getConflictRead((w, locW, xW), RW):
		return [(r, locR, xR) for (r, locR, xR) in getReads(RW) if eq(locR, locW) ]

	# print getConflictRead(writes[2], RW)

	w0 = Const('w0', WriteOp)

	# print [
	# 	(locW, locR)
	# 	# if eq(locW, locR)
	# 	# else Not(fr(r,w))
	# 	for (w, locW, vW) in writes for (r, locR, vR) in reads
	# ]

	axiom = [
		# fr(getSymbolic(r), getSymbolic(w)) == Exists([w0], And(restrict(w0, writes, WriteOp),rf(w0, getSymbolic(r)), co(w0,getSymbolic(w))))
		# for w in writes for r in getConflictRead(w, RW)
		fr(r, w) == Exists(w0, And( restrict(w0, writes, WriteOp), rf(w0, r), co(w0, w) ))
		if (eq(locW, locR))
		else Not(fr(r,w))
		for (w, locW, vW) in writes for (r, locR, vR) in reads
	]
	return (fr, axiom)

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

# WR
rfe = Function('rfe', Event, Event, BoolSort())
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

if __name__ == '__main__':

	def evaluate_r(fp, r, Ev):
		print str(r)+' = ' + str([
			 (x,y) 
			for x in Ev for y in Ev if (fp.query(r(x,y)) == sat)
		])

	# x, y, z = Consts('a b c', Event)
	# i, j = Consts('i j', Event)
	# (po_r, axioms1) = relation('po_r',Event, [(x,y), (y,z)])
	# print acyclic(po_r)

	# locations
	x = new_loc()
	y = new_loc()
	# registers
	x1 = Val.register(0)
	y1 = Val.register(1)

	# Message passing 
	# Reads 
	# Ry1, Rx1

	Ry1 = new_read('Ry1', y, y1, 2)
	Rx1 = new_read('Rx1', x, x1, 2)
	# Writes
	# Wx1, Ry1
	Wx1 = new_write('Wx1', x, 1, 1)
	Wy1 = new_write('Wy1', y, 1, 1)
	# initialValue
	Wx0 = new_write('Wx0', x, 0, 0)
	Wy0 = new_write('Wy0', y, 0, 0)

	PoSet = [(Wx0, Wx1),(Wy0, Wx1), (Wx1,Wy1), (Ry1,Rx1)]
	EV_S = [Ry1, Rx1, Wx1, Wy1, Wx0, Wy0]


	fp = Fixedpoint()
	# fp.set(print_with_fixedpoint_extensions=False, compile_with_widening = True)
	fp.set(engine='pdr')

	is_read = Function('is_read', Event, BoolSort())
	is_write = Function('is_write', Event, BoolSort())
	conflict = Function('conflict', Event, Event, BoolSort())

	fp.register_relation(is_read, is_write, conflict)

	read = Event.read
	write = Event.write

	fp.vars = []
	eid = Int('eid')
	loc = Const('loc', Loc)
	r = Const('reg', Val)
	pid = Int('pid')
	fp.declare_var(eid, loc, r, pid)
	print Rx1
	fp.rule(is_read(read(eid, loc, r, pid)))
	fp.rule(is_write(write(eid, loc, r, pid)))


	# execution
	(fp,po) = program_order(fp, PoSet)
	(fp,co) = conflict_order(fp, EV_S)
	(fp,rf) = read_from(fp, EV_S)

	fp.vars = []
	# e = Const('e', Event)
	# fp.add(Exists(e, co(e,Rx1)))
	fp.add(po(Wx1,Wx0))
	# fp.add(po(Wx0,Wx1))

	print fp
	print fp.query()
