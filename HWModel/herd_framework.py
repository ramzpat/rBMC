# herd_framework

from z3 import *

# Abstract model def 
Proc = 		IntSort()			 			# Processor
Loc = 		DeclareSort('Loc')				# Location
Instr = 	DeclareSort('Instr')			# Instruction 
Val = 		IntSort()						# Value in the systems

Event =		DeclareSort('Event')
RW = 		DeclareSort('RW')
ReadOp = 	DeclareSort('ReadOp')			# Read access 	*A kind of memory operation(MemOp)
WriteOp = 	DeclareSort('WriteOp')			# Write access 	*A kind of memory operation(MemOp) 

idW = Function('idW', WriteOp, IntSort())
idR = Function('idR', ReadOp, IntSort())
idLoc = Function('idLoc', Loc, IntSort())

proc = Function('proc', Event, Proc)
proc.domain = (lambda i: Event)

w1, w2 = Consts('w1 w2', WriteOp)
r1, r2 = Consts('r1 r2', ReadOp)
l1, l2 = Consts('l1 l2', Loc)
global_axioms = [ ForAll([w1, w2], Implies(idW(w1) != idW(w2), w1 != w2 ) ),  
				  ForAll([r1, r2], Implies(idR(r1) != idR(r2), r1 != r2 ) ),
				  ForAll([l1, l2], Implies(idLoc(l1) != idLoc(l2), l1 != l2))]

# Wrap function for subsort 
def subsort_f(sort1, sort2):
	f_sort = Function('wrap_'+str(sort1)+'_'+str(sort2), sort1, sort2)
	return f_sort 

E_RW = subsort_f(RW, Event)
unknow_event = Const('unknow_event', Event)
Event.cast = (lambda val:
	val if (type(val) != tuple and val.sort() == Event) else
	E_RW(RW.cast(val)) if (RW.cast(val) != unknow_rw or val.sort() == RW)
	else val if (val.sort() == Event)
	else unknow_event
	)

RW_R = subsort_f(ReadOp, RW)
RW_W = subsort_f(WriteOp, RW)
unknow_rw = Const('unknow_rw', RW)
RW.cast = (lambda val:
	RW.cast(getSymbolic(val)) if (type(val) == tuple)
	else RW_R(ReadOp.cast(val)) if (val.sort() == ReadOp)
	else RW_W(val) if (val.sort() == WriteOp)
	else val if (val.sort() == RW)
	else unknow_rw
	)
unknow_read = Const('unkwown_read', ReadOp)
ReadOp.cast = (lambda val:
 	val if (val.sort() == ReadOp)
	else unknow_read
	)
unknow_write = Const('unknow_write', WriteOp)
WriteOp.cast = (lambda val:
	val if (val.sort() == WriteOp)
	else unknow_write
	)

id_loc = 0
def new_loc(name):
	global global_axioms
	global id_loc

	loc = Const(name, Loc)
	global_axioms += [idLoc(loc) == id_loc]
	id_loc += 1
	return loc

id_read = 0
def new_read(name, location, val, pid = 0):
	global global_axioms
	global id_read 

	read = Const(name, ReadOp)
	loc = Const(location, Loc)
	v = Const(val, Val)

	global_axioms += [idR(read) == id_read, proc(read) == pid]
	id_read += 1

	return (read, loc, v)


id_write = 0
def new_write(name, location, val, pid = 0):

	global global_axioms
	global id_write

	write = Const(name, WriteOp)
	loc = Const(location, Loc)
	v = val if type(val) == int else Const(val, Val)

	global_axioms += [idW(write) == id_write, proc(write) == pid]
	id_write += 1
	return (write, loc, v)

def getSymbolic((rw, loc, proc)):
	return rw

def getWrites(RW):
	return [w for w in RW if (getSymbolic(w).sort() if type(w) == tuple else w.sort()) == WriteOp]
def getReads(RW):
	return [r for r in RW if (getSymbolic(r).sort() if type(r) == tuple else r.sort()) == ReadOp]

def isWrite(rw):
	return getSymbolic(rw).sort() == WriteOp
def isRead(rw):
	return getSymbolic(rw).sort() == ReadOp
# utilities

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
# reflexive-transitive (r*)
def reflexive_transitive(r_name, r):
	domX = r.domain(0)
	domY = r.domain(1)

	ref_r = Function(r_name, domX, domY, BoolSort())

	x = Const('x', domX)
	y = Const('y', domY)
	z = Const('z', domY)

	return (ref_r, 
			[ForAll([x,y], ref_r(x,y) == Or(r(x,y),
											x == y,
											Exists([z], And(ref_r(x,z), ref_r(z,y)))
											))])

def seqRelation(r_name, r1, r2):
	dom = r1.domain(0)
	seqR = Function(r_name, dom, dom, BoolSort())
	x, y, z = Consts('x y z', dom)
	return (seqR,
		[ForAll([x,z], seqR(x,z) == Exists([y], And(r1(x,y),r2(y,z)) ))]
		)


# acyclic / irreflexive
def acyclic(name, r, sets = []):
	dom = r.domain(0)
	x, y = Consts('x y', dom)
	(r_trans,axiom) = transitive(name, r, sets)
	return (r_trans, axiom + [Not(Exists([x], r_trans(x,x) ))])

# Relation with trasitive and irreflexive
def program_order(Set = [], sets = []):
	(r, axioms1) = relation('po_rel', Event, Set)
	# r = Function('po_relation', Event, Event, BoolSort())
	# po = Function('po', Event, Event, BoolSort())

	# x, y = Consts('x y', Event)
	(po, axioms2) = acyclic('po', r, sets)
	po.domain = (lambda i: Event)
	return (po, axioms1 + axioms2)


# Execution (E, po, rf, co)
# co - coherrence 
def conflict_order(Set = []):
	def conflict_def((x,locA,pA), (y,locB,pB)):
		return (x.sort() == WriteOp or y.sort() == WriteOp) and (eq(locA,locB))

	def conflict_writes(Set = []):
		return [ (x,y) for x in Set for y in Set if not(eq(getSymbolic(x),getSymbolic(y))) and 
						getSymbolic(x).sort() == WriteOp and getSymbolic(y).sort() == WriteOp 
					 and conflict_def(x,y)]

	co_rel = Function('co_rel', WriteOp, WriteOp, BoolSort())
	co = Function('co', WriteOp, WriteOp, BoolSort())
	co.domain = (lambda i: WriteOp)

	w1 = Const('temp_w1', WriteOp)
	w2 = Const('temp_w2', WriteOp)

	conf_w = conflict_writes(Set) 
	conf_w2 = conf_w + [(y,x) for (x,y) in conf_w]
	# print conf_w
	# relation
	axiom = [ForAll([w1,w2], co_rel(w1, w2) ==  Or([And(w1 == WriteOp.cast(getSymbolic(i)), w2 == WriteOp.cast(getSymbolic(j))) for (i,j) in conf_w2]))]
	# asymetric : choose one of them
	u = Const('Wx1', WriteOp)
	v = Const('Wx0', WriteOp)
	# axiom += [ ForAll([w1,w2], Xor( co_rel(w1, w2), co_rel(w2,w1) )) ]
	# axiom += [ co(u, v) ]

	axiom += [ForAll([w1, w2], co(w1, w2) == And(co_rel(w1, w2), 
												# asymetric
												Not(co(w2, w1))) )]
	# axiom += [co(w1, w2) == And(co_rel(w1, w2), Not(co(w2, w1)))  for ((w1, loc, x1), (w2, loc, x2)) in conf_w2]
	return (co, axiom)

# rf - one to many
def read_from(Set = []):

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

	# rf_rel = Function('rf_rel', WriteOp, ReadOp, BoolSort()))
	rf = Function('rf', WriteOp, ReadOp, BoolSort())
	# one to many (read can read from only one write)
	x = Const('x', WriteOp)
	y = Const('y', ReadOp)

	read = [r for r in Set if getSymbolic(r).sort() == ReadOp]
	write = [w for w in Set if getSymbolic(w).sort() == WriteOp]
	candidate_rf = conflict_rf(Set)
	

	axiom = [
		# relation
		# ForAll([x,y], rf(x,y) == Or([ And(x == getSymbolic(w), y == getSymbolic(r)) for (w,r) in candidate_rf ])),
		# one to many ?
		And( [ Or([rf(getSymbolic(w), getSymbolic(r)) for w in candidate_writes(r, Set)]) for r in read  ] ), 
		# rf-val
		And( [ 
			Implies( rf(w,r), (vA == vB) )
			for ((w, locA, vA), (r, locB, vB)) in candidate_rf]
			),
		# rf-loc
		# rf-val
		And( [ 
			Implies( rf(w,r), (locA == locB) )
			for (w, locA, vA) in write for (r, locB, vB) in read ]
			)
	]
	# print axiom
	return (rf, axiom)


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

rfe = Function('rfe', WriteOp, ReadOp, BoolSort())
def rfe_axiom(RW = []):
	writes = getWrites(RW)
	reads = getReads(RW)
	return [
		rfe(w,r) == And(rf(w,r), proc(w) != proc(r))
		for (w, locW, vW) in writes for (r, locR, vR) in reads 
	]

hb = Function('hb', Event, Event, BoolSort())
hb.domain = (lambda i: Event)
def hb_axiom(RW = []):
	global hb
	return [
		hb(x,y) == simplify(Or([
			# ppo(x,y), fences(x,y),
			( rfe(x,y) if (x.sort() == WriteOp) and (y.sort() == ReadOp) else False )
			]
			))
		for (x, locX, v1) in RW for (y, locY, v2) in RW
	]

noThinAir = Function('no_thin_air', Event, Event, BoolSort())
noThinAir.domain = (lambda i: Event)
def no_thin_air_axiom(RW = []):
	e = Const('e', Event)
	axiom = [
		noThinAir(x,y) == Or(
				hb(x,y), 
				Exists(e, And(restrict(e, RW, Event), noThinAir(x, e), noThinAir(e,y)))
			)
		# if not(eq(x,y))
		# else Not(noThinAir(x,y))
		for (x, locX, v1) in RW for (y, locY, v2) in RW
	] 
	axiom += [ # acyclic
		ForAll(e, Not(noThinAir(e,e)))
	]
	return axiom
# observ = irreflexive(fre;prop;hb*)
def observation(RW = []):
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

	writes = getWrites(RW)
	reads = getReads(RW)

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
				Exists(e, And(restrict(e, RW, Event), hb(x,e), hb(e,y)))
			])
		for (x, locX, v1) in RW for (y, locY, v2) in RW
	]
	axiom += [
		And(
		# (fre;prop)
		freProp(x,y) == Exists(w, And(restrict(w, writes, WriteOp), fre(x,w), prop(w, y))),
		# (fre;prop;hb*)
		frePropHbST(x,y) == And( Exists(e, And(restrict(e, RW, Event), freProp(x,e), hbRT(e,y))) )
		)
		for (x, locX, v1) in reads for (y, locY, v2) in RW
	]
	axiom += [
		# irreflexive(fre;prop;hb*)
		ForAll([w], Not(frePropHbST(w,w)))
	]

	return axiom

# propagation = acyclic(co U prop)
def propagation(RW = []):
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
			Exists(e, And(restrict(e, RW, Event), prog(x,e), prog(e,y)))
			])) 
		# if not(eq(x,y)) else Not(prog(x,y))
		for (x, locX, v1) in RW for (y, locY, v2) in RW
	]
	axiom += [
		# acyclic
		ForAll(e, Not(prog(e,e)))
	]
	return axiom


# arch = (ppo, fences, prop)
def sc_constraints(RW = []):
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

def tso_constraints(RW = []):
	# ppo = po\WR
	# ffence = mfence
	# lwfence = empty
	# fences = ffence U lwfence
	# prop = ppo U fences U rfe U fr

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

if __name__ == '__main__':
	x, y, z = Consts('a b c', Event)
	i, j = Consts('i j', Event)
	# (po_r, axioms1) = relation('po_r',Event, [(x,y), (y,z)])
	# print acyclic(po_r)

	# print reflexive_transitive('po', po_r)

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

	RW_S = [Ry1, Rx1, Wx1, Wy1, Wx0, Wy0]

	# execution
	(po, axiom_po) = program_order([(Wx0, Wx1),(Wy0, Wx1), (Wx1,Wy1), (Ry1,Rx1)], RW_S)
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

	s.add(sc_constraints(RW_S))

	# print s
	# s.add((po((Wx1),getSymbolic(Wy1))))
	# print ((po(Wx1,Wy1)))
	
	x1 = Int('x1')
	y1 = Int('y1')
	s.add(y1 == 1)
	s.add(x1 == 1)

	u = Const('Wx0', WriteOp)
	v = Const('Wx1', WriteOp)
	# s.add(And(po(u,v), co(v, u)))
	res = s.check()
	print res

	if res == sat:
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


