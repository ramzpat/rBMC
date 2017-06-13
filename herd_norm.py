from Arch.arch_object import *

# Normamlize 
def Norm(R, cs = True):
	if len(R) == 0:
		return []

	r = R[0]
	if isinstance(r, i_assignment):
		if isinstance(r.expression, i_if_exp):
			re = r.expression
			new_r1 =  i_if(cs & re.cond , [ i_assignment( r.var, re.t_exp) ] )
			new_r2 = i_if(cs & ~re.cond, [ i_assignment( r.var, re.f_exp) ] )
			return [new_r1, new_r2] + Norm(R[1:], cs)
		else:
			return [ i_if(cs, [r] ) ] + Norm(R[1:], cs)
	elif isinstance(r, i_write):
		return [ i_if(cs, [r] ) ] + Norm(R[1:], cs)
	elif isinstance(r, InstrAssume):
		return [ i_if(cs, [r] ) ] + Norm(R[1:], cs)
	elif isinstance(r, InstrAssert):
		return [ i_if(cs, [r] ) ] + Norm(R[1:], cs)
	elif isinstance(r, i_if):
		return Norm(r.statement, (cs & r.cond)) + Norm(R[1:], cs)
	elif r == None:
		return Norm(R[1:], cs)
	else:
		print R
		# return 
	return []