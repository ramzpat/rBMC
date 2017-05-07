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


def restrict(e, sets = []):
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
def program_order(s, PoSet = [], Ev = []):
	po = Function('po', Event, Event, BoolSort())
	# s.register_relation(po)
	# (po_rel, ax) = relation('po_rel', Event, PoSet)
	# s.add(ax)

	x, y, z = Consts('x y z', Event)
	# s.add(ForAll([x,y], po(x,y) == Or(po_rel(x,y), 
	# 								Exists(z, And(po(x,z), po(z,y)))
	# 								)))

	for (i,j) in poS:
		s.add(po(i, j)) 
	s.add(ForAll([x,y,z], Implies(And(po(x,y), po(y,z)), po(x,z))))
	
	s.add(ForAll(x,Not(po(x,x))))
	s.add(ForAll([x,y],Implies(And(po(x,y)), Not(po(y,x)))))

	return (s, po)


# Execution (E, po, rf, co)
# co - coherrence 
def conflict_order(s, Ev = []):
	co = Function('co', Event, Event, BoolSort())

	for e1 in Ev:
		for e2 in Ev:
			# if eq(e1.target, e2.target) and not(eq(e1.arg(0),e2.arg(0))):
			# 	print str((e1,e2)) + ': ' + str(eq(e1.target, e2.target))
			s.add(
				co(e1, e2) == (
					And(Distinct(e1, e2),
						Not(co(e2, e1)),
						e1.target == e2.target
						)
					if not(eq(e1.arg(0),e2.arg(0))) and isWrite(e1) and isWrite(e2) else False
					)
				)
			# if not(eq(e1.arg(0),e2.arg(0))) and isWrite(e1) and isWrite(e2):
			# 	print e1.target
			# 	print e2.target
			# 	print co(e1, e2) == (
			# 		And(Distinct(e1, e2),
			# 			Not(co(e2, e1),
			# 			e1.target == e2.target
			# 			)
			# 		if not(eq(e1.arg(0),e2.arg(0))) and isWrite(e1) and isWrite(e2) else False
			# 		)
			# 	)
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
	# s.register_relation(rf)
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
			# print Or([rf(w, e1) for w in cWrite ])
			# print And([
			# 	Implies(rf(w, e1), w.val == e1.val)
			# 	for w in cWrite
			# 	])
		else:
			s.add(ForAll(e, Not(rf(e,e1))))

	return (s, rf)

def iico_relation(s, S = []):
	(iico, axiom) = relation('iico', Event, S)
	s.add(axiom)
	return (s, iico)

def rf_reg_relation(s, Ev = []):
	def candidate_writes(r, Ev = []):
		write =[w for w in Ev if isWriteReg(w) and eq(w.target, r.target) ]
		return write

	# rf : W-reg x R-reg relation
	e = Const('e', Event)
	rf_reg = Function('rf-reg', Event, Event, BoolSort())
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
	# s.register_relation(dd_reg)
	e1, e2, e3 = Consts('e1 e2 e3', Event)
	# s.declare_var(e1, e2, e3)
	# s.rule(dd_reg(e1, e2), rf_reg(e1, e2)) 
	# s.rule(dd_reg(e1, e2), iico(e1, e2))
	# s.rule(dd_reg(e1, e3), [dd_reg(e1, e2), dd_reg(e2, e3)])
	# s.vars = []
	s.add(
		ForAll([e1, e2], Implies(rf_reg(e1, e2), dd_reg(e1, e2))),
		ForAll([e1, e2], Implies(iico(e1, e2), dd_reg(e1, e2))),
		ForAll([e1, e2, e3], Implies(And(dd_reg(e1, e2), dd_reg(e2, e3)), dd_reg(e1, e3)))
		)

	return (s, dd_reg)

# addr dependency = dd-reg ^ RM
def addr_dependency(s, dd_reg, Ev = []):
	addr_dep = Function('addr_dep',Event, Event, BoolSort())
	# s.register_relation(addr_dep)

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
	# s.register_relation(data_dep)

	for e1 in Ev:
		for e2 in Ev:
			if isRead(e1) and isWrite(e2):
				s.add(data_dep(e1, e2) == And(dd_reg(e1, e2)))
			else:
				s.add(Not(data_dep(e1, e2)))
	return (s, data_dep)

# RB
def ReadBranchRelation(s, Ev = []):
	RB = Function('RB', Event, Event, BoolSort())
	for r in Ev:
		for b in Ev:
			s.add( RB(r, b) if isRead(r) and isBranch(b) else Not(RB(r, b)) )
	return (s, RB)

# ctrl = (dd_reg ^ RB);po
def ctrl_dependency(s, dd_reg, RB, po):
	ctrl = Function('ctrl', Event, Event, BoolSort())
	# s.register_relation(ctrl)	

	e1, e2, b = Consts('e1 e2 b', Event)
	# s.declare_var(e1, e2, b)
	# s.rule(ctrl(e1, e2), [ isRead(e1), isBranch(b), dd_reg(e1,b), po(b, e2) ])
	# s.vars = []
	s.add(ForAll([e1, e2, b], Implies( And(dd_reg(e1, b), RB(e1, b), po(b, e2)), ctrl(e1, e2) ) ))
	return (s, ctrl)

# fr - fromread (fixed point) 
def from_read(s, rf, co):
	fr = Function('fr', Event, Event, BoolSort())
	# s.register_relation(fr)

	e1, e2, e3 = Consts('e1 e2 e3', Event)
	# s.declare_var(e1,e2,e3)
	# invrf = rf^-1
	# fr = (invrf ; co) \ id
	# s.rule(fr(e1,e3), [rf(e2, e1), co(e2, e3), e1 != e3])
	# s.vars = []
	s.add( ForAll([e1, e2, e3], Implies( And(rf(e2, e1), co(e2, e3), Distinct(e1, e3)), fr(e1, e3) ) ) )
	return (s, fr)

def irreflexive(s, r):
	e = Const('e', Event)
	s.add(ForAll(e, Not(r(e,e))))
	return (s, r)


def sc_constraints(s, po, fr, rf, co):
	# sc.cat
	# SC ----------
	# (* Atomic *)
	# empty rmw & (fre;coe) as atom  
	# s.add(Not( ) )
	# (* Sequential consistency *)
	# acyclic po | fr | rf | co as sc
	(s, trans) = (acyclic(s, po, fr, rf, co))
	return s

def tso_constraints(s, po, rf, fr, co, Ev):
	# tso-01.cat
	# (* Communication relations that order events*)
	# let com-tso = rfe | co | fr
	# (* Program order that orders events *)
	# let po-tso = po & (W*W | R*M)
	rfe = Function('rfe', Event, Event, BoolSort())
	for e1 in Ev:
		for e2 in Ev:
			s.add(rfe(e1, e2) == And(rf(e1,e2), Not(e1.pid == e2.pid)))
			
	com_tso = Function('com_tso', Event, Event, BoolSort())
	for e1 in Ev:
		for e2 in Ev:
			s.add(com_tso(e1, e2) == Or(rfe(e1,e2), co(e1, e2), fr(e1, e2)))
	po_tso = Function('po_tso', Event, Event, BoolSort())
	for e1 in Ev:
		for e2 in Ev:
			s.add((po_tso(e1, e2) == po(e1,e2)) if isRead(e1) or isWrite(e2) else Not(po_tso(e1, e2)) )

	# (* TSP global-happens-before *)
	# let ghb = po-tso | com-tso
	# acyclic ghb

	(s, ghb) = acyclic(s, com_tso, po_tso)
	return s
	# show ghb

	return s

def pso_constraints(s, po, rf, fr, co, Ev):
	# tso-01.cat
	# (* Communication relations that order events*)
	# let com-tso = rfe | co | fr
	# (* Program order that orders events *)
	# let po-pso = po & (R*M) 
	rfe = Function('rfe', Event, Event, BoolSort())
	for e1 in Ev:
		for e2 in Ev:
			s.add(rfe(e1, e2) == And(rf(e1,e2), Not(e1.pid == e2.pid)))
			
	com_tso = Function('com_tso', Event, Event, BoolSort())
	for e1 in Ev:
		for e2 in Ev:
			s.add(com_tso(e1, e2) == Or(rfe(e1,e2), co(e1, e2), fr(e1, e2)))
	po_tso = Function('po_tso', Event, Event, BoolSort())
	for e1 in Ev:
		for e2 in Ev:
			s.add((po_tso(e1, e2) == po(e1,e2)) if isRead(e1) else Not(po_tso(e1, e2)) )

	# (* TSP global-happens-before *)
	# let ghb = po-tso | com-tso
	# acyclic ghb

	(s, ghb) = acyclic(s, com_tso, po_tso)
	return s
	# show ghb

	return s

def arm_constraints(s, po_loc, rf, fr, co, addr, data, ctrl, Ev):
	# (* Uniproc *)
	# acyclic po-loc | rf | fr | co as uniproc
	(s, uniproc) = acyclic(s, po_loc, rf, fr, co)

	# (* Atomic *)
	# empty rmw & (fre;coe) as atomic

	# (* Utilities *)
	# let dd = addr | data
	# let rdw = po-loc & (fre;rfe)
	# let detour = po-loc & (coe ; rfe)
	# let addrpo = addr;po
	dd = Function('dd', Event, Event, BoolSort())
	rdw = Function('rdw', Event, Event, BoolSort())
	detour = Function('detour', Event, Event, BoolSort())
	addrpo = Function('addrpo', Event, Event, BoolSort())

	rfe = Function('rfe', Event, Event, BoolSort())
	rfi = Function('rfi', Event, Event, BoolSort())
	fre = Function('fre', Event, Event, BoolSort())
	coe = Function('coe', Event, Event, BoolSort())

	for e1 in Ev:
		for e2 in Ev:
			s.add(rfe(e1, e2) == And(rf(e1,e2), Not(e1.pid == e2.pid)))
			s.add(rfi(e1, e2) == And(rf(e1,e2), (e1.pid == e2.pid)))
			s.add(fre(e1, e2) == And(fr(e1,e2), Not(e1.pid == e2.pid)))
			s.add(coe(e1, e2) == And(co(e1,e2), Not(e1.pid == e2.pid)))

	e1, e2, e3, e4 = Consts('e1 e2 e3 e4', Event)
	s.add(ForAll([e1, e2], dd(e1, e2) == Or(addr(e1, e2), data(e1, e2))))
	s.add(ForAll([e1, e2, e3],Implies(And(po_loc(e1, e2), fre(e1, e3), rfe(e3, e2) ), rdw(e1, e2)) ))
	s.add(ForAll([e1, e2, e3],Implies(And(po_loc(e1, e2), coe(e1, e3), rfe(e3, e2) ), detour(e1, e2)) ))
	s.add(ForAll([e1, e2, e3], Implies( And(addr(e1, e3), po(e3, e2)), addrpo(e1, e2) ) ))

	# (*******)
	# (* ppo *)
	# (*******)

	# include "armfences.cat"

	# (* Initial value *)
	# let ci0 = ctrlisb | detour
	# let ii0 = dd | rfi | rdw
	# let cc0 = dd | ctrl | addrpo (* po-loc deleted *)
	# let ic0 = 0
	ctrlisb = Function('ctrlisb', Event, Event, BoolSort())
	s.add(ForAll([e1, e2], Not(ctrlisb(e1, e2))))
	ci0 = Function('ci0', Event, Event, BoolSort())
	ii0 = Function('ii0', Event, Event, BoolSort())
	cc0 = Function('cc0', Event, Event, BoolSort())
	ic0 = Function('ic0', Event, Event, BoolSort())
	s.add(ForAll([e1, e2], ci0(e1, e2) == Or(ctrlisb(e1, e2), detour(e1, e2))))
	s.add(ForAll([e1, e2], ii0(e1, e2) == Or(dd(e1, e2), rfi(e1, e2), rdw(e1, e2))))
	s.add(ForAll([e1, e2], cc0(e1, e2) == Or(dd(e1, e2), ctrl(e1, e2), addrpo(e1, e2))))
	s.add(ForAll([e1, e2], Not(ic0(e1, e2))))

	# (* Computes ppo the ARM and PPC way *)

	# (* Fixpoint from i -> c in instructions and transitivity *)
	# let rec ci = ci0 | (ci;ii) | (cc;ci)
	# and ii = ii0 | ci | (ic;ci) | (ii;ii)
	# and cc = cc0 | ci | (ci;ic) | (cc;cc)
	# and ic = ic0 | ii | cc | (ic;cc) | (ii ; ic) (* | ci inclus dans ii et cc *)

	# rec = Function('rec', Event, Event, BoolSort())
	ci = Function('ci', Event, Event, BoolSort())
	ii = Function('ii', Event, Event, BoolSort())
	cc = Function('cc', Event, Event, BoolSort())
	ic = Function('ic', Event, Event, BoolSort())

	s.add(	ForAll([e1, e2], Implies( ci0(e1, e2), ci(e1, e2) ) ),
			ForAll([e1, e2, e3], Implies( And(ci(e1,e2), ii(e2, e3)), ci(e1, e3) )),
			ForAll([e1, e2, e3], Implies( And(cc(e1, e2), ci(e2, e3)), ci(e1, e3) ))
		)
	s.add(	ForAll([e1, e2], Implies( ii0(e1, e2), ii(e1, e2))),
			ForAll([e1, e2], Implies( ci(e1, e2), ii(e1, e2))),
			ForAll([e1, e2, e3], Implies( And(ic(e1, e2), ci(e2, e3)), ii(e1, e3) )),
			ForAll([e1, e2, e3], Implies( And(ii(e1, e2), ii(e2, e3)), ii(e1, e3) ))
		)
	s.add(	ForAll([e1, e2], Implies( cc0(e1,e2), cc(e1,e2))),
			ForAll([e1, e2, e3], Implies( ci(e1, e2), cc(e1,e2))), 
			ForAll([e1, e2, e3], Implies( And(ci(e1, e2), ci(e2, e3)), cc(e1, e3))), 
			ForAll([e1, e2, e3], Implies( And(cc(e1, e2), cc(e2, e3)), cc(e1, e3)))
		)
	s.add(	ForAll([e1, e2], Implies(ic0(e1, e2), ic(e1, e2))),
			ForAll([e1, e2], Implies(ii(e1, e2), ic(e1, e2))),
			ForAll([e1, e2], Implies(cc(e1, e2), ic(e1, e2))),
			ForAll([e1, e2, e3], Implies( And(ic(e1, e2), cc(e2, e3)), ic(e1, e3) )),
			ForAll([e1, e2, e3], Implies( And(ii(e1, e2), ic(e2, e3)), ic(e1, e3) )),
		)

	# let ppo =
	#   let ppoR = ii & (R * R)
	#   and ppoW = ic & (R * W) in
	#   ppoR | ppoW
	ppoR = Function('ppoR', Event, Event, BoolSort())
	ppoW = Function('ppoW', Event, Event, BoolSort())
	for x in Ev:
		for y in Ev:
			s.add(ppoR(x,y) == And( ii(x,y), (isRead(x) and isRead(y)) ))
			s.add(ppoW(x,y) == And( ic(x,y), (isRead(x) and isWrite(y)) ))

	ppo = Function('ppo', Event, Event, BoolSort())
	s.add(ForAll([e1,e2], ppo(e1, e2) == Or(ppoR(e1, e2), ppoW(e1, e2))))

	# (**********)
	# (* fences *)
	# (**********)

	# (* ARM *)
	# let WW = W * W
	# let dmb.st=dmb.st & WW
	# let dsb.st=dsb.st & WW


	# (* Common, all arm barriers are strong *)
	# let strong = dmb|dsb|dmb.st|dsb.st
	# let light = 0

	# PCChecks

	# let fence = strong|light

	fence = Function('fence', Event, Event, BoolSort())
	s.add(ForAll([e1, e2], Not(fence(e1, e2))))

	# (* happens before *)
	# let hb = ppo | fence | rfe
	# acyclic hb as thinair
	hb = Function('hb', Event, Event, BoolSort())
	s.add(ForAll([e1, e2], hb(e1, e2) == Or( ppo(e1, e2), fence(e1, e2), rfe(e1, e2) )))

	(s, thinair) = acyclic(s, ppo, fence, rfe)

	# (* prop *)
	# let hbstar = hb*
	# let propbase = (fence|(rfe;fence));hbstar
	hbstar = Function('hb*', Event, Event, BoolSort())
	s.add( ForAll([e1, e2], Implies(hb(e1, e2), hbstar(e1, e2)) ) )
	s.add( ForAll([e1, e2, e3], Implies( And(hbstar(e1,e2), hbstar(e2,e3)), hbstar(e1,e3) )))
	# s.add(  )

	propbase = Function('propbase', Event, Event, BoolSort())
	rfefence = Function('rfe;fence', Event, Event, BoolSort())
	s.add(ForAll([e1, e2, e3], Implies( And(rfe(e1, e2), fence(e2,e3)), rfefence(e1, e3) ) ))
	s.add(ForAll([e1, e2, e3], Implies( And( Or(fence(e1, e2), rfefence(e1,e2)), hbstar(e2,e3) ), propbase(e1,e3) ) ))

	# let chapo = rfe|fre|coe|(fre;rfe)|(coe;rfe)
	chapo = Function('chapo', Event, Event, BoolSort())
	s.add(ForAll([e1, e2], Implies(rfe(e1,e2), chapo(e1,e2))))
	s.add(ForAll([e1, e2], Implies(fre(e1,e2), chapo(e1,e2))))
	s.add(ForAll([e1, e2], Implies(coe(e1,e2), chapo(e1,e2))))
	s.add(ForAll([e1, e2, e3], Implies( And( fre(e1,e2), rfe(e2,e3) ), chapo(e1,e3) )))
	s.add(ForAll([e1, e2, e3], Implies( And( coe(e1,e2), rfe(e2,e3) ), chapo(e1,e3) )))

	# let prop = propbase & (W * W) | (chapo? ; propbase*; strong; hbstar)

	# acyclic co|prop as propagation
	# irreflexive fre;prop;hbstar as observation

	# let xx = po & (X * X)
	# acyclic co | xx as scXX



	return s

def power_constraints(Ev = []):
	# ffence = sync 
	# lwfence = lwsync \ WR

	# Propogation order for Power
	# 

	axioms = []
	return axioms

# constraining 
def acyclic(s, *rel):
	trans = Function('acyclic' + str(rel), Event, Event, BoolSort())
	# s.register_relation(trans)
	e1, e2, e3 = Consts('e1 e2 e3', Event)
	# s.declare_var(e1, e2, e3)
	for r in rel:
		# s.rule(trans(e1, e2), r(e1, e2))
		s.add( ForAll([e1, e2], Implies(r(e1, e2), trans(e1, e2)) ))
	# s.rule(trans(e1, e2), [trans(e1, e3), trans(e3, e2)])
	s.add(ForAll([e1, e2, e3], Implies(And(trans(e1, e2), trans(e2, e3)), trans(e1, e3)) ))
	s.add(ForAll(e1, Not(trans(e1, e1))))
	# s.vars = []
	return (s,trans)

if __name__ == '__main__':
	# try ARM models

	s = Solver()
	# s = Fixedpoint()
	# s.set(engine='pdr')

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
	(s, po) = program_order(s, poS, Ev1 + Ev2)
	#  - co : W x W relation
	(s, co) = conflict_order(s, Ev1 + Ev2)
	#  - rf : W x R relation
	(s, rf) = read_from(s, Ev1 + Ev2)
	
	po_loc = Function('po-loc', Event, Event, BoolSort())
	e1, e2 = Consts('e1 e2', Event)
	for e1 in Ev1 + Ev2:
		for e2 in Ev1 + Ev2:
			s.add(po_loc(e1, e2) == And(po(e1, e2), (e1.target == e2.target) if e1.target.sort() == e2.target.sort() else False ))
			# print (po_loc(e1, e2) == And(po(e1, e2), (e1.target == e2.target) if e1.target.sort() == e2.target.sort() else False ))

	# Instruction semantics level
	#  - iico : E x E relation
	(s, iico) = iico_relation(s, iicoS)
	#  - rf-reg : W-reg x R-reg relation
	(s, rf_reg) = rf_reg_relation(s, Ev1 + Ev2)

	cfence = Function('cfence', Event, Event, BoolSort())
	# s.register_relation(cfence)

	#  -- dependency relation
	#  - dd_reg
	(s, dd_reg) = dd_reg_relation(s, rf_reg, iico)
	(s, addr_dep) = addr_dependency(s, dd_reg, Ev1 + Ev2)
	(s, data_dep) = data_dependency(s, dd_reg, Ev1 + Ev2)
	(s, RB) = ReadBranchRelation(s, Ev1 + Ev2)
	(s, ctrl) = ctrl_dependency(s, dd_reg, RB, po)
	(s, ctrl_cfence) = ctrl_dependency(s, dd_reg, RB, cfence)
	
	(s, fr) = from_read(s, rf, co)

	fre = Function('fre', Event, Event, BoolSort())
	fri = Function('fri', Event, Event, BoolSort())
	# s.register_relation(fre, fri)

	for e1 in Ev1 + Ev2:
		for e2 in Ev1 + Ev2:
			s.add(fre(e1, e2) == And(fr(e1,e2), Not(e1.pid == e2.pid)))
			s.add(fri(e1, e2) == And(fr(e1,e2), (e1.pid == e2.pid)))

	
	# s = sc_constraints(s, po, fr, rf, co)
	# s = tso_constraints(s, po, rf, fr, co, Ev1 + Ev2)
	# s = pso_constraints(s, po, rf, fr, co, Ev1 + Ev2)
	s = arm_constraints(s, po_loc, rf, fr, co, addr_dep, data_dep, ctrl, Ev1 + Ev2)

	# check prob
	# s.add(po(Wy0, Wx0))
	# s.add(Rr1_1.val == 1)
	# s.add(Rvr5.val == 1)
	# s.add(Rvr4.val == 0)
	print s.check()


