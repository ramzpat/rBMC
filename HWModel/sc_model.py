# sc_model

from model import *
import hw_z3 as hw

class SCModel(HWModel):

	def __str__(self):
		return "SC model"

	# Relations
	spo = Function('spo', hw.Opr, hw.Opr, BoolSort()) 	# Significant program order
	sco = Function('sco', hw.Opr, hw.Opr, BoolSort())		# Significant conflict order
	
	# Helping_relation
	loopRel = Function('loopRel', hw.Opr, hw.Opr, BoolSort())	

	spo.domain = (lambda i: hw.Opr)
	sco.domain = (lambda i: hw.Opr)
	loopRel.domain = (lambda i: hw.Opr) 

	rw1, rw2 = Consts('rw1 rw2', hw.MemOp)
	a, b = 	Consts('a b', hw.Opr)
	r = Const('r', hw.ReadOp)
	w = Const('w', hw.WriteOp)
	r1, r2 = Consts('r1 r2', hw.ReadOp)
	w1, w2 = Consts('w1 w2', hw.WriteOp)
	i, j = Consts('i j', hw.Proc)

	def model_axioms(self, info):
		return self.sc_axioms

	# Conditions 
	sc_axioms = [
		# SPO Def
		ForAll([rw1, rw2],
			Implies(And(
				hw.po(rw1, rw2), 
				# Not(conflict(rw1, rw2))
				Not(hw.mem_access(rw1) == hw.mem_access(rw2))
				),
				spo(rw1, rw2)) 
			),
		# SCO Def
		ForAll([rw1, rw2], 
			Implies(hw.ico(rw1, rw2), sco(rw1, rw2))
			),
		ForAll([r1, r2, w], 
			Implies(
				And(hw.ico(r1, w), hw.ico(w, r2)),
				sco(r1, r2))
			),
		# Uniprocessor cond (RW -po-> W)
		ForAll([rw1, w, i],
			Implies(
				And(
					hw.conflict(rw1, w),
					hw.po(rw1, w),
				),
				hw.xo(hw.subOpr(rw1,i), hw.subOpr(w, i)) 
				)
			),
		# Coherence (W -co'-> W)
		ForAll([w1, w2, i],
			Implies(
				And(
					hw.conflict(w1, w2),
					hw.ico(w1, w2),
					),
				hw.xo(hw.subOpr(w1,i), hw.subOpr(w2, i)) 
				)
			),
		# LoopRel def (Base case)
		ForAll([rw1, rw2],
			Implies(sco(rw1, rw2),
				loopRel(rw1, rw2))
			),
		# LoopRel def (Inductive case)
		ForAll([rw1, rw2,a, b, i],
			Implies(
				And(loopRel(rw1, a),
					spo(a, b),
					sco(b, rw2)
					),
				loopRel(rw1, rw2))
			),
		# Multi-proc 1
		ForAll([w1, r, rw2, i],
			Implies(
				And(hw.conflict(w1, rw2),
					hw.ico(w1, r),
					hw.po(r, rw2),
					),
				hw.xo(hw.subOpr(w1, i), hw.subOpr(rw2, i)))
			),
		# Multi-proc 2
		ForAll([rw1, rw2, a, b, i],
			Implies(And(
					hw.conflict(rw1, rw2),
					spo(rw1, a),
					loopRel(a, b),
					spo(b, rw2),
					),
				hw.xo(hw.subOpr(rw1, i), hw.subOpr(rw2, i)))
			),
		# Multi-proc 3
		ForAll([w1, r2, i, r, a, b],
			Implies(And(
					hw.conflict(w1, r2),
					sco(w1, r),
					spo(r, a), 
					loopRel(a, b),
					spo(b, r2),
					),
				hw.xo(hw.subOpr(w1, i), hw.subOpr(r2, i)))
			),
	]

spo = SCModel.spo
sco = SCModel.sco
