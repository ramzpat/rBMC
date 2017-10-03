
# ----------------- Operations
# class Operation(AnnotatedStatement):
class Operation():
	def __init__(self):
		pass 
	def clone(self):
		return self.__class__()
	def __str__(self):
		return 'nop'

# <var> := <exp>
# <var> ::= <reg> | <loc> | <symbolic var>
class Assignment(Operation):
	def __init__(self, var, exp):
		self.var = var
		self.exp = exp
	def clone(self):
		return self.__class__(self.var.clone(), self.exp)

	def __str__(self):
		return str(self.var) + " := " + str(self.exp) + ' (' + str(self.__class__) + ')' 

# <loc> := <val> {symbolic / concrete}
class WriteAssn(Assignment):
	pass 

# <reg> := <val> {symbolic / concrete}
class ReadAssn(Assignment):
	pass 

class SyncOpr(Operation):
	pass
	 
# ll(tempReg, Loc)
class OprLoadLink(SyncOpr):
	def __init__(self, var, loc):
		self.var = var 
		self.loc = loc 
	def __str__(self):
		return str(self.var) +' := load-link(' + str(self.loc) + ')'
	def clone(self):
		return self.__class__(self.var.clone(), self.loc.clone())

class OprStoreCond(SyncOpr):
	def __init__(self, var, loc, exp):
		self.var = var 
		self.loc = loc 
		self.exp = exp 
	def __str__(self):
		return str(self.var) + ' := store-cond(' + str(self.loc) + "," + str(self.exp) + ')'
	def clone(self):
		return self.__class__(self.var.clone(), self.loc.clone(), self.exp.clone())

# fence()
class fenceStm(Operation):
	def __init__(self):
		pass
	def clone(self):
		return self.__class__()
	def __str__(self):
		return 'fence()' 
		
class branchOp(Operation):
	def __init__(self, cond, label, fake_op = False):
		self.cond = cond
		self.label = label
		self.fake_op = fake_op
	def clone(self):
		return self.__class__(self.cond, self.label, self.fake_op)
	def __str__(self):
		return 'branch(' + str(self.cond) + ', ' + str(self.label) + ')'
