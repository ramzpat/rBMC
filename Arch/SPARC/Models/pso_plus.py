# PSO+ Model

if __package__ is None:
  import sys
  from os import path
  sys.path.append( path.dirname(path.dirname(path.dirname( path.dirname( path.abspath(__file__) ) ) )))
  from HWModel.model import *
  import HWModel.hw_z3 as hw
else:
  from HWModel.model import *
  import HWModel.hw_z3 as hw

from z3 import *


class PSOPlusModel(HWModel):

	def __str__(self):
		return "PSO+ Model"

	# Additional Op
	MembarWR =	DeclareSort('MEMBAR(WR)')				# MEMBER(WR) operation in TSO+ (spac v8+) 
	STBar = DeclareSort('STBar')

	membarOp = Function('f_membar', MembarWR, hw.FenceOp)	# a wrapper function
	stbarOp = Function('f_stbar', STBar, hw.FenceOp)	# a wrapper function
	
	def __init__(self):
		hw.FenceOp.cast = (lambda val:
			val if (val.sort() == hw.FenceOp)
			else self.stbarOp(val) if (val.sort() == self.STBar)
			else self.membarOp(val)
		)

	# Relations
	spo = Function('spo', hw.Opr, hw.Opr, BoolSort()) 	# Significant program order
	spo1 = Function('spo1', hw.Opr, hw.Opr, BoolSort()) 	# Significant program order spo'
	spo2 = Function('spo2', hw.Opr, hw.Opr, BoolSort()) 	# Significant program order spo''
	sco = Function('sco', hw.Opr, hw.Opr, BoolSort())		# Significant conflict order
	loopRel = Function('loopRel', hw.Opr, hw.Opr, BoolSort())	# Helping_relation

	# xo_mul1 = Function('xo_mul1', SubOpr, SubOpr, BoolSort())
	# xo_mul2 = Function('xo_mul1', SubOpr, SubOpr, BoolSort())
	# xo_mul3 = Function('xo_mul1', SubOpr, SubOpr, BoolSort())

	spo.domain = (lambda i: hw.Opr)
	spo1.domain = (lambda i: hw.Opr)
	spo2.domain = (lambda i: hw.Opr)
	sco.domain = (lambda i: hw.Opr)
	loopRel.domain = (lambda i: hw.Opr) 


	def spo_relation(self, info):
		# return []
		po = info['po']
		reads = info['MemOp']['read']
		writes = info['MemOp']['write']
		rmw = info['MemOp']['rmw']
		spo1 = self.spo1
		spo2 = self.spo2
		spo  = self.spo
		sco = self.sco
		MembarWR = self.MembarWR
		STBar = self.STBar

		def is_PO(po, x, y):
			result = False
			for p in po:
				result = is_po(p, x, y)
				if result:
					break
			return result

		x, y = Consts('x y', hw.MemOp)
		

		# spo'(X,Y) if ...
		#   R -po-> RW
		# 	W -po-> W
		# 	W -po-> MEMBAR(WR) -po-> R

		SPO = [ ForAll([x], Not( spo(x,x) )) ]
		SPO1 = [ ForAll([x], Not( spo1(x,x) )) ]
		SPO2 = [ ForAll([x], Not( spo2(x,x) )) ]

		write_p_rmw = writes + [(hw.atomic_write(a),l,i) for (a, l, i) in rmw]
		read_p_rmw = reads + [(hw.atomic_read(a),l,i) for (a, l, i) in rmw]
		
		rw1, rw2, rw3 = Consts('rw1 rw2 rw3', hw.MemOp)
		r = Const('tempR', hw.ReadOp)
		w1, w2 = Consts('tempW1 tempW2', hw.WriteOp)
		wr = Const('wr_fence', MembarWR)
		st = Const('st_fence', STBar)
		a_rmw = Const('a_rmw', hw.AtomicOp)

		SPO2 += [
			ForAll([rw1, rw2], 
				# R -po-> RW
				If(Exists([r], And(restrict(r, read_p_rmw), rw1 == hw.read(r), hw.po(r, rw2))), 
					spo2(rw1, rw2), 
				# W -po-> STBAR -po-> W 
				If(Exists([w1, w2, st], And(Not(w1 == w2), restrict(w1, write_p_rmw), restrict(w2, write_p_rmw), 
										rw1 == hw.write(w1), rw2 == hw.write(w2), hw.po(w1, st), hw.po(st, w2))),
					spo2(rw1, rw2),
				# W -po-> MEMBAR(WR) -po-> R
				If(Exists([w1, r, wr], And(restrict(w1, write_p_rmw), restrict(r, read_p_rmw), 
										rw1 == hw.write(w1), rw2 == hw.read(r),
										hw.po(w1, wr), hw.po(wr, r))), 
					spo2(rw1, rw2), 
				Not(spo2(rw1, rw2)))
				))
				)
		]

		SPO1 += [
			ForAll([rw1, rw2],
				# W (in RMW) -po-> R
				If( Exists([a_rmw, r], And(restrict(a_rmw, rmw), restrict(r, read_p_rmw), 
											rw1 == write(hw.atomic_write(a_rmw)), rw2 == hw.read(r),
											hw.po(rw1, rw2))),
				spo1(rw1, rw2), Not(spo1(rw1, rw2)))
				)

		]

		memOps = [ (hw.MemOp.cast(rw),l,i) for (rw, l, i) in write_p_rmw + read_p_rmw]
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
	def sco_relation(self, info):

		po = info['po']
		reads = info['MemOp']['read']
		writes = info['MemOp']['write']
		rmw = info['MemOp']['rmw']
		spo1 = self.spo1
		spo2 = self.spo2
		spo  = self.spo
		sco = self.sco
		MembarWR = self.MembarWR

		write_p_rmw = writes + [(hw.atomic_write(a),l,i) for (a, l, i) in rmw]
		read_p_rmw = reads + [(hw.atomic_read(a),l,i) for (a, l, i) in rmw]
		memOps = [ (hw.MemOp.cast(rw),l,i) for (rw, l, i) in write_p_rmw + read_p_rmw]

		x, y = Consts('x y', hw.MemOp)
		r1, r2 = Consts('r1 r2', hw.ReadOp)
		w = Const('w', hw.WriteOp)

		SCO = [ ForAll([x], Not(sco(x,x))) ]

		SCO += [
			ForAll([x, y],
				If(And(restrict(x,memOps), restrict(y,memOps), hw.co(x,y)), sco(x,y),
				If(Exists([r1,r2, w], And(Not(r1 == r2), restrict(r1, read_p_rmw), restrict(r2, read_p_rmw),
										restrict(w, write_p_rmw),
										hw.read(r1) == x, hw.read(r2) == y, hw.co(x,w), hw.co(w,y) )), 
					sco(x,y), Not(sco(x,y)))
				)
			)
		]

		return SCO
	def model_axioms(self, info):
		# return self.tso_axioms

		# Relations
		spo = self.spo
		spo1 = self.spo1
		spo2 = self.spo2
		sco = self.sco
		loopRel = self.loopRel

		# ------ variables 
		rw1, rw2, rw3 = Consts('rw1 rw2 rw3', hw.MemOp)
		a, b = 	Consts('a b', hw.Opr)
		r = Const('r', hw.ReadOp)
		w = Const('w', hw.WriteOp)
		r1, r2 = Consts('r1 r2', hw.ReadOp)
		w1, w2 = Consts('w1 w2', hw.WriteOp)
		i, j = Consts('i j', hw.Proc)

		# stbar = Const('stbar', FenceOp)
		rmw = Const('rmw', hw.AtomicOp)
		memb_wr = Const('membar_wr', self.MembarWR)

		# Conditions 
		tso_axioms = [		
			# % Uniproc RW -po-> W
			# xo(subOpr(X,I), subOpr(Y,I)) :- conflict(X,Y), subOpr(X,I), subOpr(Y,I), pOrder(X,Y), isWrite(Y), isRW(X).
			ForAll([rw1, w2, i],
				Implies(
					And(
						hw.conflict(rw1, w2),
						hw.po(rw1, w2),
					),
					hw.xo(hw.subOpr(rw1, i), hw.subOpr(w2, i))
				)
			),

			# % Coherence W -co-> W 
			# xo(subOpr(X,I), subOpr(Y,I)) :- conflict(X,Y), subOpr(X,I), subOpr(Y,I), isWrite(X), isWrite(Y), co(X,Y).
			ForAll([w1, w2, i],
				Implies(
					And(
						hw.conflict(w1, w2), 
						hw.co(w1, w2),
					),
					hw.xo(hw.subOpr(w1, i), hw.subOpr(w2, i))
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

			# % util-func   X -sco-> ... -spo-> Y 
			ForAll([rw1, rw2],
			If( sco(rw1, rw2), loopRel(rw1, rw2),
				If( Exists([a,b], And(loopRel(rw1,a), spo(a, b), sco(b, rw2)) ) , 
					loopRel(rw1, rw2) , Not(loopRel(rw1, rw2)) )
				)
			),

			ForAll([rw1, rw2],
				Implies(loopRel(rw1,rw2), rw1 != rw2)
			),

			# % Multi - 2
			# % RW -spo-> { A -sco-> B -spo-> }+ RW *)
			# xo(subOpr(RW,I), subOpr(RW2,I)) :- conflict(RW,RW2), subOpr(RW,I), subOpr(RW2,I), isRW(RW), isRW(RW2), spo(RW,AA), loopRel(AA,BB), spo(BB,RW2). 
			ForAll([rw1, rw2, a, b, i],
				Implies(
					And(
						hw.conflict(rw1, rw2),
						spo(rw1, a),
						loopRel(a, b),
						spo(b, rw2),
					),
					hw.xo(hw.subOpr(rw1, i), hw.subOpr(rw2, i))
				)
			),

			# % Multi - 3
			# %% W -sco-> R -spo-> { A -sco-> B -spo-> }+ R
			# xo(subOpr(W,I), subOpr(R2,I)) :- conflict(W,R2), subOpr(W,I), subOpr(R2,I), isWrite(W), isRead(R), isRead(R2), sco(W,R), spo(R,AA), loopRel(AA,BB), spo(BB,R2). 
			ForAll([w1, r2, i, a, b, r],
				Implies(
					And(
						hw.conflict(w1, r2),
						sco(w1, r),
						spo(r, a),
						loopRel(a, b),
						spo(b, r2),  
					),
					hw.xo(hw.subOpr(w1, i), hw.subOpr(r2, i))
				)
			),
		]
		return (tso_axioms) + self.spo_relation(info) + self.sco_relation(info)

if __name__ == "__main__":
	print "[Debug]"

	pass
# MembarWR = TSOPlusModel.MembarWR
# membarOp = TSOPlusModel.membarOp

