# herd_framework

from z3 import *
from relation_util import *

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

def new_read(location, val, pid = 0):
	global eidCnt
	if is_reg(location):
		read = ReadReg(eidCnt, location, val, pid) #Const(name, ReadReg)
	else:
		read = ReadOp(eidCnt, location, val, pid) #Const(name, ReadOp)
	
	read.eid = eidCnt
	read.target = location
	read.val = val
	read.pid = pid
	eidCnt += 1
	return read
	

def new_write(location, val, pid = 0):
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
	write.eid = eidCnt
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

	# r = Function(r_name, Dom, Dom, BoolSort())
	# x, y = Consts('x y', Dom)
	# ax = 

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
	# print PoSet
	for (i,j) in PoSet:
		s.add(po(i, j)) 
	# s.add(ForAll([x,y,z], Implies(And(po(x,y), po(y,z)), po(x,z))))
	
	# s.add(ForAll(x,Not(po(x,x))))
	# s.add(ForAll([x,y],Implies(And(po(x,y)), Not(po(y,x)))))

	# po_rel = transitive_closure(poS)
	# prepare po transitivity
	newPo = []
	EvID = [0 for i in range(0, eidCnt)]
	for (i,j) in PoSet:
		newPo += [(i.eid, j.eid)]
		EvID[i.eid] = i
		EvID[j.eid] = j
	newPo = transitive_closure(newPo)

	for x in Ev:
		for y in Ev:
			s.add(po(x,y) if (x.eid,y.eid) in newPo else Not(po(x,y)) )
	return (s, po, newPo)


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

def iico_relation(s, S = [], Ev = []):
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
	for e1 in Ev:
		for e2 in Ev:
			if (e1.eid, e2.eid) in idS:
				s.add( iico(e1, e2) )	
				iicoSet += [(e1.eid, e2.eid)]
			else:
				s.add(Not(iico(e1, e2)))

	return (s, iico, iicoSet)

def rf_reg_relation(s, Ev = []):
	def candidate_writes(r, Ev = []):
		write =[w for w in Ev if isWriteReg(w) and eq(w.target, r.target) ]
		return write

	# rf : W-reg x R-reg relation
	e = Const('e', Event)
	rf_reg = Function('rf-reg', Event, Event, BoolSort())
	rf_regSet = []
	for e1 in Ev:
		if isReadReg(e1):
			cWrite = candidate_writes(e1, Ev)
			print e1
			assert(len(cWrite) == 1)
			# there are only one correspond write in ssa form
			s.add(rf_reg(cWrite[0], e1))
			# rf-val
			s.add(cWrite[0].val == e1.val)
			rf_regSet += [(cWrite[0].eid, e1.eid)]
			# rf-loc
		else:
			s.add(ForAll(e, Not(rf_reg(e,e1))))
	return (s, rf_reg, rf_regSet)

# dd-reg = (rf-reg U iico)+
def dd_reg_relation(s, rf_regSet, iicoSet, Ev):
	dd_reg = Function('dd_reg', Event, Event, BoolSort())
	e1, e2, e3 = Consts('e1 e2 e3', Event)
	union = set(rf_regSet) | set(iicoSet)
	union = transitive_closure(union)
	# s.add(
	# 	ForAll([e1, e2], Implies(rf_reg(e1, e2), dd_reg(e1, e2))),
	# 	ForAll([e1, e2], Implies(iico(e1, e2), dd_reg(e1, e2))),
	# 	ForAll([e1, e2, e3], Implies(And(dd_reg(e1, e2), dd_reg(e2, e3)), dd_reg(e1, e3)))
	# 	)

	# s.add([dd_reg(e1, e2) == Or(
	# 								rf_reg(e1, e2), iico(e1, e2),
	# 								Exists(e3, And(restrict(e3, Ev), dd_reg(e1, e3), dd_reg(e3, e2)))
	# 							) for e1 in Ev for e2 in Ev] )
	# print set(rf_regSet)
	# print set(iicoSet)
	# print union
	s.add([ dd_reg(e1, e2) if (e1.eid, e2.eid) in union else Not(dd_reg(e1, e2)) for e1 in Ev for e2 in Ev])
	return (s, dd_reg, union)

# addr dependency = dd-reg ^ RM
def addr_dependency(s, dd_regSet, Ev = []):
	addr_dep = Function('addr_dep',Event, Event, BoolSort())
	# s.register_relation(addr_dep)

	# e1, e2, e3 = Consts('e1 e2 e3', Event)
	# s.declare_var(e1, e2, e3)
	addrSet = []
	for e1 in Ev:
		for e2 in Ev:
			if isRead(e1) and isRW(e2) and (e1.eid, e2.eid) in dd_regSet:
				s.add(addr_dep(e1, e2))
				addrSet += (e1.eid, e2.eid)
			else:
				s.add(Not(addr_dep(e1, e2)))
	# s.vars = []
	return (s, addr_dep, addrSet)

# data dep = dd-reg ^ RW
def data_dependency(s, dd_regSet, Ev = []):
	data_dep = Function('data_dep', Event, Event, BoolSort())
	# s.register_relation(data_dep)
	dataSet = []
	for e1 in Ev:
		for e2 in Ev:
			if isRead(e1) and isWrite(e2) and (e1.eid, e2.eid) in dd_regSet:
				s.add(data_dep(e1, e2))
				dataSet += (e1.eid, e2.eid)
			else:
				s.add(Not(data_dep(e1, e2)))
	return (s, data_dep, dataSet)

# RB
def ReadBranchRelation(s, Ev = []):
	RB = Function('RB', Event, Event, BoolSort())
	rbSet = []
	for r in Ev:
		for b in Ev:
			if isRead(r) and isBranch(b):
				s.add( RB(r, b) )
				rbSet += [(r.eid, b.eid)]
			else:
				s.add( Not(RB(r, b)))
	return (s, RB, rbSet)

# ctrl = (dd_reg ^ RB);po
def ctrl_dependency(s, dd_regSet, rbSet, poSet, Ev):
	ctrl = Function('ctrl', Event, Event, BoolSort())
	
	andSet = set(dd_regSet) & set(rbSet)
	concat = concat_relation(andSet, poSet)

	# s.declare_var(e1, e2, b)
	# s.rule(ctrl(e1, e2), [ isRead(e1), isBranch(b), dd_reg(e1,b), po(b, e2) ])
	# s.vars = []
	# s.add(ForAll([e1, e2, b], Implies( And(dd_reg(e1, b), RB(e1, b), po(b, e2)), ctrl(e1, e2) ) ))

	for e1 in Ev:
		for e2 in Ev:
			if (e1.eid, e2.eid) in concat:
				s.add( ctrl(e1, e2) )
			else:
				s.add( Not(ctrl(e1, e2)))

	return (s, ctrl, concat)

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

def irreflexive(s, r):
	e = Const('e', Event)
	s.add(ForAll(e, Not(r(e,e))))
	return s

def empty(s, r):
	empty = Function('empty_' + str(r), Event, Event, BoolSort())
	e1, e2 = Consts('e1 e2', Event)
	s.add(ForAll([e1, e2], Not(e1, e2)))
	return (s, r)

def sc_constraints(s, po, rf, fr, co, Ev = []):
	# sc.cat
	# SC ----------
	# (* Atomic *)
	# empty rmw & (fre;coe) as atom  
	# s.add(Not( ) )
	# (* Sequential consistency *)
	# acyclic po | fr | rf | co as sc
	(s, trans) = (acyclic(s, po, fr, rf, co))
	return s

def tso_constraints(s, po, poSet, rf, fr, co, Ev):
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

	# prepare for uniproc
	po_loc = Function('po-loc', Event, Event, BoolSort())
	po_locSet = [ (e1.eid, e2.eid) for e1 in Ev for e2 in Ev if (e1.eid, e2.eid) in poSet and (eq(e1.target, e2.target) if e1.target.sort() == e2.target.sort() else False) ]
	s.add([po_loc(e1, e2) == And(po(e1, e2), (e1.target == e2.target) if e1.target.sort() == e2.target.sort() else False )  for e1 in Ev for e2 in Ev])

	rfi = Function('rfi', Event, Event, BoolSort())
	fri = Function('fri', Event, Event, BoolSort())
	for e1 in Ev:
		for e2 in Ev:
			s.add(rfi(e1, e2) == And(rf(e1,e2), (e1.pid == e2.pid)))
			s.add(fri(e1, e2) == And(fr(e1,e2), (e1.pid == e2.pid)))

	# (* Uniproc check specialized for TSO *)
	# irreflexive po-loc & (R*W); rfi as uniprocRW
	# irreflexive po-loc & (W*R); fri as uniprocWR
	uniprocRW = Function('uniprocRW', Event, Event, BoolSort())
	uniprocWR = Function('uniprocWR', Event, Event, BoolSort())

	po_loc_RW = Function('po-loc(RW)', Event, Event, BoolSort())
	po_loc_WR = Function('po-loc(WR)', Event, Event, BoolSort())
	s.add([po_loc_RW(e1, e2) == And(po_loc(e1, e2), True if isRead(e1) and isWrite(e2) else False )  for e1 in Ev for e2 in Ev])
	s.add([po_loc_WR(e1, e2) == And(po_loc(e1, e2), True if isWrite(e1) and isRead(e2) else False )  for e1 in Ev for e2 in Ev])
	e1, e2, e3 = Consts('e1 e2 e3', Event)
	s.add(ForAll([e1, e2, e3], Implies(And(po_loc_RW(e1,e2), rfi(e2,e3)), uniprocRW(e1,e3))))
	s.add(ForAll([e1, e2, e3], Implies(And(po_loc_WR(e1,e2), fri(e2,e3)), uniprocWR(e1,e3))))
	s = irreflexive(s, uniprocRW)
	s = irreflexive(s, uniprocWR)

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

def arm_constraints(s, po, rf, fr, co, iico, rf_reg, poSet, iicoSet, rf_regSet, Ev):
	
	po_loc = Function('po-loc', Event, Event, BoolSort())
	po_locSet = [ (e1.eid, e2.eid) for e1 in Ev for e2 in Ev if (e1.eid, e2.eid) in poSet and (eq(e1.target, e2.target) if e1.target.sort() == e2.target.sort() else False) ]
	s.add([po_loc(e1, e2) == And(po(e1, e2), (e1.target == e2.target) if e1.target.sort() == e2.target.sort() else False )  for e1 in Ev for e2 in Ev])
	
	cfence = Function('cfence', Event, Event, BoolSort())
	s.add([Not(cfence(e1, e2)) for e1 in Ev for e2 in Ev])
	
	rmw = Function('rmw', Event, Event, BoolSort())			
	s.add([Not(rmw(e1, e2)) for e1 in Ev for e2 in Ev])

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

	#  -- dependency relation
	#  - dd_reg
	(s, dd_reg, dd_regSet) = dd_reg_relation(s, rf_regSet, iicoSet, Ev)
	(s, addr, addrSet) = addr_dependency(s, dd_regSet, Ev)
	(s, data, dataSet) = data_dependency(s, dd_regSet, Ev)
	(s, RB, rbSet) = ReadBranchRelation(s, Ev)
	(s, ctrl, ctrlSet) = ctrl_dependency(s, dd_regSet, rbSet, poSet, Ev)
	(s, ctrl_cfence, ctrl_cfenceSet) = ctrl_dependency(s, dd_regSet, rbSet, [], Ev)

	# (* Uniproc *)
	# acyclic po-loc | rf | fr | co as uniproc
	(s, uniproc) = acyclic(s, po_loc, rf, fr, co)

	# (* Atomic *)
	# empty rmw & (fre;coe) as atomic
	e1, e2, e3 = Consts('e1 e2 e3', Event)
	frecoe = Function('fre;coe', Event, Event, BoolSort())
	s.add( ForAll([e1, e2, e3], Implies( And(fre(e1, e3), coe(e3, e2)), frecoe(e1, e2) )) )
	s.add( ForAll([e1, e2], Not( And( rmw(e1,e2), frecoe(e1, e2) ) )))


	# (* Utilities *)
	# let dd = addr | data
	# let rdw = po-loc & (fre;rfe)
	# let detour = po-loc & (coe ; rfe)
	# let addrpo = addr;po
	dd = Function('dd', Event, Event, BoolSort())
	rdw = Function('rdw', Event, Event, BoolSort())
	detour = Function('detour', Event, Event, BoolSort())
	addrpo = Function('addrpo', Event, Event, BoolSort())
	
	e1, e2, e3, e4 = Consts('e1 e2 e3 e4', Event)
	# s.add(ForAll([e1, e2], dd(e1, e2) == Or(addr(e1, e2), data(e1, e2))))
	# s.add(ForAll([e1, e2, e3],Implies(And(po_loc(e1, e2), fre(e1, e3), rfe(e3, e2) ), rdw(e1, e2)) ))
	# s.add(ForAll([e1, e2, e3],Implies(And(po_loc(e1, e2), coe(e1, e3), rfe(e3, e2) ), detour(e1, e2)) ))
	# s.add(ForAll([e1, e2, e3], Implies( And(addr(e1, e3), po(e3, e2)), addrpo(e1, e2) ) ))
	ddSet = set(addrSet) | set(dataSet)
	s.add([ dd(e1, e2) if (e1.eid, e2.eid) in ddSet else Not(dd(e1, e2)) for e1 in Ev for e2 in Ev ])
	# rdwSet = set(po_locSet & concat_relation(fre))
	s.add([ rdw(e1, e2) == 		(And(po_loc(e1, e2), Exists(e3, And(restrict(e3, Ev), fre(e1,e3), rfe(e3,e2)) ) ))  for e1 in Ev for e2 in Ev])
	s.add([ detour(e1, e2) == 	(And(po_loc(e1, e2), Exists(e3, And(restrict(e3, Ev), coe(e1,e3), rfe(e3,e2)) ) ))  for e1 in Ev for e2 in Ev])
	# s.add([ addrpo(e1, e2) == 	(Exists(e3, And(restrict(e3, Ev), addr(e1,e3), po(e3,e2)) ) )  for e1 in Ev for e2 in Ev])
	addrpoS = concat_relation(addrSet, poSet)
	s.add([ addrpo(e1, e2) if (e1.eid, e2.eid) in addrpoS else Not(addrpo(e1,e2)) for e1 in Ev for e2 in Ev ])

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
	s.add([ Not(ctrlisb(e1, e2)) for e1 in Ev for e2 in Ev])

	ci0 = Function('ci0', Event, Event, BoolSort())
	ii0 = Function('ii0', Event, Event, BoolSort())
	cc0 = Function('cc0', Event, Event, BoolSort())
	ic0 = Function('ic0', Event, Event, BoolSort())
	e1, e2 = Consts('e1 e2', Event)
	s.add(ForAll([e1, e2], ci0(e1, e2) == Or(ctrlisb(e1, e2), detour(e1, e2))))
	s.add(ForAll([e1, e2], ii0(e1, e2) == Or(dd(e1, e2), rfi(e1, e2), rdw(e1, e2))))
	s.add(ForAll([e1, e2], cc0(e1, e2) == Or(dd(e1, e2), ctrl(e1, e2), addrpo(e1, e2))))
	s.add(ForAll([e1, e2], Not(ic0(e1, e2))))
	# s.add([(ci0(e1, e2) == Or(ctrlisb(e1, e2), detour(e1, e2))) for e1 in Ev for e2 in Ev])
	# s.add([ ci0(e1, e2) == Or(ctrlisb(e1, e2), detour(e1, e2)) for e1 in Ev for e2 in Ev])
	# s.add([ ii0(e1, e2) == Or(dd(e1, e2), rfi(e1, e2), rdw(e1, e2)) for e1 in Ev for e2 in Ev])
	# s.add([ cc0(e1, e2) == Or(dd(e1, e2), ctrl(e1, e2), addrpo(e1, e2)) for e1 in Ev for e2 in Ev])
	# s.add([ Not(ic0(e1, e2)) for e1 in Ev for e2 in Ev])

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
	
	e1, e2, e3, e4 = Consts('e1 e2 e3 e4', Event)

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
	s.add([ppo(e1, e2) == Or(ppoR(e1, e2), ppoW(e1, e2)) for e1 in Ev for e2 in Ev])

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
	e1, e2, e3, e4 = Consts('e1 e2 e3 e4', Event)
	strong = Function('strong', Event, Event, BoolSort())
	light = Function('light', Event, Event, BoolSort())
	s.add(ForAll([e1, e2], Not(strong(e1, e2))))
	s.add(ForAll([e1, e2], Not(light(e1, e2))))

	# PCChecks

	# let fence = strong|light

	fence = Function('fence', Event, Event, BoolSort())
	s.add([ Not(fence(e1, e2)) for e1 in Ev for e2 in Ev])

	# (* happens before *)
	# let hb = ppo | fence | rfe
	# acyclic hb as thinair
	hb = Function('hb', Event, Event, BoolSort())
	s.add([ hb(e1, e2) == Or( ppo(e1, e2), fence(e1, e2), rfe(e1, e2) ) for e1 in Ev for e2 in Ev])
	(s, thinair) = acyclic(s, hb)

	# (* prop *)
	# let hbstar = hb*
	# let propbase = (fence|(rfe;fence));hbstar
	hbstar = Function('hb*', Event, Event, BoolSort())
	e1, e2 = Consts('e1 e2', Event)
	s.add( ForAll([e1], hbstar(e1, e1)))
	s.add( ForAll([e1, e2], Implies(hb(e1, e2), hbstar(e1, e2))) )
	s.add( ForAll([e1, e2, e3], Implies( And(hbstar(e1,e2), hbstar(e2,e3)), hbstar(e1,e3) )))
	# s.add([ hbstar(e1, e2) if eq(e1, e2) else ( Or(hb(e1, e2), 
	# 											Exists(e3, And(restrict(e3, Ev), hbstar(e1,e3), hbstar(e3,e2)))) ) 
	# 		for e1 in Ev for e2 in Ev ])

	propbase = Function('propbase', Event, Event, BoolSort())
	rfefence = Function('rfe;fence', Event, Event, BoolSort())
	s.add(ForAll([e1, e2, e3], Implies( And(rfe(e1, e2), fence(e2,e3)), rfefence(e1, e3) ) ))
	s.add(ForAll([e1, e2, e3], Implies( And( Or(fence(e1, e2), rfefence(e1,e2)), hbstar(e2,e3) ), propbase(e1,e3) ) ))
	# s.add([ rfefence(e1, e2) == Exists(e3, And(restrict(e3, Ev), rfe(e1, e3), fence(e3, e2))) for e1 in Ev for e2 in Ev ])
	# s.add([ propbase(e1,e2) == Exists(e3, And(restrict(e3, Ev), Or(fence(e1, e3), rfefence(e1,e3)), hbstar(e3, e2))) for e1 in Ev for e2 in Ev ])

	# let chapo = rfe|fre|coe|(fre;rfe)|(coe;rfe)
	chapo = Function('chapo', Event, Event, BoolSort())
	s.add(ForAll([e1, e2], Implies(rfe(e1,e2), chapo(e1,e2))))
	s.add(ForAll([e1, e2], Implies(fre(e1,e2), chapo(e1,e2))))
	s.add(ForAll([e1, e2], Implies(coe(e1,e2), chapo(e1,e2))))
	s.add(ForAll([e1, e2, e3], Implies( And( fre(e1,e2), rfe(e2,e3) ), chapo(e1,e3) )))
	s.add(ForAll([e1, e2, e3], Implies( And( coe(e1,e2), rfe(e2,e3) ), chapo(e1,e3) )))
	# s.add([chapo(e1, e2) == Or(rfe(e1, e2), fre(e1, e2), coe(e1, e2), 
	# 						Exists(e3, And(restrict(e3, Ev), Or(
	# 														And(fre(e1, e3), rfe(e3, e2)),
	# 														And(coe(e1, e3), rfe(e3, e2))
	# 														)))
	# 					) for e1 in Ev for e2 in Ev] )

	# let prop = propbase & (W * W) | (chapo? ; propbase*; strong; hbstar)
	prop = Function('prob', Event, Event, BoolSort())
	chapoIden = Function('chapo?', Event, Event, BoolSort())
	propbaseStar = Function('propbase*', Event, Event, BoolSort())
	s.add(ForAll([e1, e2], chapoIden(e1,e2) == Or(e1 == e2, chapo(e1, e2)) ))
	s.add(ForAll([e1], propbaseStar(e1, e1)))
	s.add(ForAll([e1,e2], Implies(propbase(e1,e2), propbaseStar(e1, e2))))
	s.add(ForAll([e1,e2,e3], Implies( And(propbaseStar(e1,e3), propbaseStar(e3,e2)), propbaseStar(e1,e2) )))

	prop2 = Function('prop2',Event, Event, BoolSort())
	e1, e2, e3, e4, e5 = Consts('e1 e2 e3 e4 e5', Event)
	s.add(ForAll([e1, e2, e3, e4, e5], Implies( And(chapoIden(e1,e2), propbaseStar(e2, e3), strong(e3, e4), hbstar(e4, e5)) , prop2(e1, e5) )))
	s.add([prop(x, y) == Or( ( propbase(x,y) if isWrite(x) and isWrite(y) else False ), (prop2(x,y)) ) for x in Ev for y in Ev])

	# acyclic co|prop as propagation
	# irreflexive fre;prop;hbstar as observation
	(s, propagation) = acyclic(s, co, prop)
	freprophbstar = Function('fre;prop;hbstar', Event, Event, BoolSort())
	s.add(ForAll([e1, e2, e3,e4], Implies(And(fre(e1,e2), prop(e2,e3), hbstar(e3, e4)), freprophbstar(e1,e4))))
	s = irreflexive(s, freprophbstar)

	# let xx = po & (X * X)
	# acyclic co | xx as scXX

	print 'hey'
	return s

def power_constraints(Ev = []):
	# ffence = sync 
	# lwfence = lwsync \ WR

	# Propogation order for Power
	# 
	axioms = []
	return axioms



def mpCheck():
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
	# loc1 = Const('loc1', Loc)
	# s.add(addrLoc(loc1) == TempAddr)

	Vr1_0 = Int('Temp1')
	Rr1_0 = new_read('Rr1_0', r1, Vr1_0, 1)
	
	Wx1 = new_write('Wx1_0', InitLoc(addrX), Vr1_0, 1)

	# str r1, [r3/y]
	TempAddr2 = Int('Temp3')
	Rr3 = new_read('Rr3_0', r3, TempAddr2, 1)
	# loc2 = Const('loc2', Loc)
	Vr1_1 = Int('Temp4')
	Rr1_1 = new_read('Rr1_1', r1, Vr1_1, 1)
	
	# s.add(addrLoc(loc2) == TempAddr2)
	Wy1 = new_write('Wy1_0', InitLoc(addrY), Vr1_1, 1)
	# print InitLoc(TempAddr2)
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
	Vloc3 = Int('Temp6')
	Rvr5 = new_read('Rvr5', InitLoc(addrY), Vloc3, 2) 
	Wr6 = new_write('Wr6', r6, Vloc3, 2)

	# ldr r7, [r4]
	Vr4 = Int('Temp7')
	Rr4 = new_read('Rr4', r4, Vr4, 2)
	Vloc4 = Int('Temp8')
	Rvr4 = new_read('Rvr4', InitLoc(addrX), Vloc4, 2) 
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
	s.add(Distinct(Ev1 + Ev2 ))

	(s, po, poS) = program_order(s, poS, Ev1 + Ev2)
	#  - co : W x W relation
	(s, co) = conflict_order(s, Ev1 + Ev2)
	#  - rf : W x R relation
	(s, rf) = read_from(s, Ev1 + Ev2)
	#  - fr : E x E relation
	(s, fr) = from_read(s, rf, co)

	# Instruction semantics level
	#  - iico : E x E relation
	(s, iico, iicoSet) = iico_relation(s, iicoS, Ev1 + Ev2)
	#  - rf-reg : W-reg x R-reg relation
	(s, rf_reg, rf_regSet) = rf_reg_relation(s, Ev1 + Ev2)


	# s = sc_constraints(s, po, rf, fr, co, Ev1 + Ev2)
	s = tso_constraints(s, po, rf, fr, co, Ev1 + Ev2)
	# s = pso_constraints(s, po, rf, fr, co, Ev1 + Ev2)


	EvID = [0 for e in Ev1 + Ev2 ]
	for e in Ev1 + Ev2:
		EvID[e.eid] = e

	# s = arm_constraints(s, po, rf, fr, co, iico, rf_reg, poS, iicoSet, rf_regSet, Ev1 + Ev2)

	# check prob
	# s.add(po(Wx0, Wy0))
	# s.add(Rr1_1.val == 2)

	s.add(Rvr5.val == 1)
	s.add(Rvr4.val == 0)
	print s.check()

def mpLoopCheck1():
	# Invariant Check
	# inv = v in {0, 1}

	s = Solver()
	
	addrX, addrY = Ints('addrX addrY')
	x = InitLoc(addrX)
	y = InitLoc(addrY)
	s.add(Distinct(x,y))
	
	# print x
	# inital value
	Wx0 = new_write(x, 0)
	Wy0 = new_write(y, 0)

	# Prepare Pid
	pid1, pid2 = Consts('pid1 pid2', Proc)
	s.add(Distinct(pid1, pid2))
	
	# P1 (pid1)
	# variables 
	# r1, r2, r3 = Consts('r1 r2 r3', Reg)
	r1 = Reg(0)
	r2 = Reg(1)
	r3 = Reg(2)

	# mov r1, #1
	Wr1 = new_write(r1, 1, 1)

	# str r1, [x]
	Vr1_0 = Int('Temp1')
	Rr1_0 = new_read(r1, Vr1_0, 1)
	Wx1 = new_write(InitLoc(addrX), Vr1_0, 1)

	# str r1, [y]
	Vr1_1 = Int('Temp4')
	Rr1_1 = new_read(r1, Vr1_1, 1)

	Wy1 = new_write(InitLoc(addrY), Vr1_1, 1)
	
	Ev1 = [Wx0, Wy0, Wr1, Rr1_0, Rr1_1, Wx1, Wy1]

	# P2 (pid2) ---------------------------
	r6 = Reg(5)
	PS2 = []
	
	# ldr r6, [y]
	Vloc3 = Int('Temp6')
	Rvr5 = new_read(InitLoc(addrY), Vloc3, 2) 
	Wr6 = new_write(r6, Vloc3, 2)

	# assert ( inv ) = ( r6 in {0,1} /\ [x] in {0,1} /\ [y] in {0,1})
	# 				 = And( Or(Vloc3 == 0, Vloc3 == 1), 
	# 						generateRead(x, valX) /\ Or(valX == 0, valX == 1),
	# 						generateRead(y, valY) /\ Or(valY == 0, valY == 1))
	valX_1 = Int('valX_1')
	assertReadX_1 = new_read(InitLoc(addrX), valX_1, 2)
	valY_1 = Int('valY_1')
	assertReadY_1 = new_read(InitLoc(addrY), valY_1, 2)
	PS2 += [ Or(valX_1 == 0, valX_1 == 1) ]
	PS2 += [ Or(valY_1 == 0, valY_1 == 1) ]
	PS2 += [ Or(Rvr5.val == 0, Rvr5.val == 1) ]



	# havoc (Wx, Wy, r6)
	hvocValX = Int('hvocValX')
	havoc_Wx = new_write(InitLoc(addrX), hvocValX, 2)
	hvocValY = Int('hvocValY')
	havoc_Wy = new_write(InitLoc(addrY), hvocValY, 2)
	hvoc_r6 = Int('hvoc_r6')
	havoc_Wr6 = new_write(r6, hvoc_r6, 2)

	# assume ( inv ) 
	valX_2 = Int('valX_2')
	assertReadX_2 = new_read(InitLoc(addrX), valX_2, 2)
	valY_2 = Int('valY_2')
	assertReadY_2 = new_read(InitLoc(addrY), valY_2, 2)
	s.add( Or(valX_2 == 0, valX_2 == 1) )
	s.add( Or(valY_2 == 0, valY_2 == 1) )
	s.add( Or(hvoc_r6 == 0, hvoc_r6 == 1) )

	# ldr r6, [y]
	Vloc3_1 = Int('Temp6_1')
	Rvr5_1 = new_read(InitLoc(addrY), Vloc3_1, 2) 
	Wr6_1 = new_write(r6, Vloc3_1, 2)

	# assert( inv )
	valX_3 = Int('valX_3')
	assertReadX_3 = new_read(InitLoc(addrX), valX_3, 2)
	valY_3 = Int('valY_3')
	assertReadY_3 = new_read(InitLoc(addrY), valY_3, 2)

	PS2 += [ Or(valX_3 == 0, valX_3 == 1) ]
	PS2 += [ Or(valY_3 == 0, valY_3 == 1) ]
	PS2 += [ Or(Vloc3_1 == 0, Vloc3_1 == 1) ]

	# --------------------------------------

	Ev2 = [Rvr5, Wr6, assertReadX_1, assertReadY_1, havoc_Wx]
	Ev2 += [havoc_Wy, havoc_Wr6, assertReadX_2, assertReadY_2, Rvr5_1, Wr6_1, assertReadX_3, assertReadY_3]


	# manual po
	poS = []
	# po for P1
	poS += [(Wx0, Wy0), (Wy0, Wr1)]
	poS += [(Wr1, Rr1_0), (Rr1_0, Wx1)]
	poS += [(Wx1, Rr1_1), (Rr1_1, Wy1)]
	# po for P2 
	# poS += [(Wy0, Wr4), (Wr4, Wr5), (Wr5, Rr5), (Rr5, Rvr5) ,(Rvr5, Wr6), (Wr6, Rr4), (Rr4, Rvr4), (Rvr4, Wr7)]
	poS += [(Wy0, Rvr5), (Rvr5, Wr6), (Wr6, assertReadX_1), (assertReadX_1, assertReadY_1), (assertReadY_1, havoc_Wx)]
	poS += [(havoc_Wx, havoc_Wy), (havoc_Wy, havoc_Wr6), (havoc_Wr6, assertReadX_2)]
	poS += [(assertReadX_2, assertReadY_2), (assertReadY_2, Rvr5_1), (Rvr5_1, Wr6_1), (Wr6_1, assertReadX_3), (assertReadX_3, assertReadY_3)]

	# manual iico
	iicoS = []
	# iico for P1 
	iicoS += [(Rr1_0, Wx1), (Rr1_1, Wy1)]
	# iico for P2
	iicoS += [(Rvr5, Wr6), (Rvr5_1, Wr6_1)]
	
	# distinct events
	s.add(Distinct(Ev1 + Ev2 ))

	(s, po, poS) = program_order(s, poS, Ev1 + Ev2)
	#  - co : W x W relation
	(s, co) = conflict_order(s, Ev1 + Ev2)
	#  - rf : W x R relation
	(s, rf) = read_from(s, Ev1 + Ev2)
	#  - fr : E x E relation
	(s, fr) = from_read(s, rf, co)

	# Instruction semantics level
	#  - iico : E x E relation
	(s, iico, iicoSet) = iico_relation(s, iicoS, Ev1 + Ev2)
	#  - rf-reg : W-reg x R-reg relation
	(s, rf_reg, rf_regSet) = rf_reg_relation(s, Ev1 + Ev2)
	# print rf_regSet

	# s = sc_constraints(s, po, rf, fr, co, Ev1 + Ev2)
	s = tso_constraints(s, po, poS, rf, fr, co, Ev1 + Ev2)

	# s = pso_constraints(s, po, rf, fr, co, Ev1 + Ev2)



	EvID = [0 for e in Ev1 + Ev2 ]
	for e in Ev1 + Ev2:
		EvID[e.eid] = e

	# s = arm_constraints(s, po, rf, fr, co, iico, rf_reg, poS, iicoSet, rf_regSet, Ev1 + Ev2)

	# check prob
	# s.add(po(Wx0, Wy0))
	# s.add(Rr1_1.val == 2)

	# s.add(Rvr5.val == 1)
	# s.add(Rvr4.val == 0)

	# print simplify(Not(And(PS2)))
	s.add(Not(And(PS2)))

	result = s.check()
	print result
	if True and result == sat:
		m = s.model()
		print m.evaluate(Rvr5)
		print m.evaluate(Wr6)
		print m.evaluate(rf(havoc_Wy,Rvr5))



if __name__ == '__main__':
	print 'hello world'
	mpLoopCheck1()
	# mpCheck()








