# Annotation


class AnnotatedStatement():
	pass 

class Assertion(AnnotatedStatement):
	def __init__(self, cond):
		self.cond = cond
	def clone(self):
		return self.__class__(self.cond)
	def __str__(self):
		return 'assert(' + str(self.cond) + ')'

class Assume(AnnotatedStatement):
	def __init__(self, cond):
		self.cond = cond
	def clone(self):
		return self.__class__(self.cond)
	def __str__(self):
		return 'assume(' + str(self.cond) + ')'

class LabelStm(AnnotatedStatement):
	def __init__(self, label):
		self.label_id = label
	def clone(self):
		return self.__class__(self.label_id)
	def __str__(self):
		return 'label(' + str(self.label_id) + ')'
Label = LabelStm

class Atomic(AnnotatedStatement):
	def __init__(self, opr):
		self.opr = opr
	def clone(self):
		return self.__class__(self.opr.clone())
	def __str__(self):
		return 'atom(' + str(self.opr) + ')'


# Havoc operator for inductive invariant
# havoc( {<var>}+ )
class havoc(AnnotatedStatement):
	def __init__(self, *v):
		self.vars = v
	def clone(self):
		return havoc(*self.vars)
	def getVars(self):
		return self.vars
	def __str__(self):
		ret = 'havoc('
		if len(self.vars) > 0:
			ret += str(self.vars[0])
		for v in self.vars[1:]:
			ret += ', ' + str(v)
		return ret + ')'


class DoWhile(AnnotatedStatement):
	def __init__(self, body, inv, branchInstr, Q = True):
		self.body = body 			# loop body
		self.bInstr = branchInstr 	# branch condition
		self.inv = inv 				# invariant
		self.Q = Q					# post-condition
	def clone(self):
		o = DoWhile(self.body.clone(), self.inv, self.bInstr)
		return o

	def strIndent(self, indent = 0):
		ret = ''
		ret += (' '* indent) + 'do{ \n'
		ret += str(self.body.strIndent(indent + 1))
		ret += (' '* indent) + '\n'
		ret += (' '* indent) + '{ '+ str(self.inv) +' }\n'
		ret += (' '* indent) + '}while('+ str(self.bInstr) +')' + '\n'
		ret += (' '* indent) + '{ '+ str(self.Q) +' }\n'
		return ret

	def __str__(self):
		return self.strIndent()


class IfBr(AnnotatedStatement):
	def __init__(self, cond, t_body, f_body = None):
		self.cond = cond 			# condition for branch
		self.t_body = t_body		# true path
		self.f_body = f_body 		# false path 

	def clone(self):
		return IfBr(self.cond, self.t_body.clone())


	def strIndent(self, indent = 0):
		ret = ''
		ret += (' '* indent) + 'if(' + str(self.cond) + '){ \n'
		ret += str(self.t_body.strIndent(indent + 1))
		ret += (' '* indent) + '\n'
		# ret += (' '* indent) + '}else{\n'
		# ret += str(self.f_body.strIndent(indent + 1))
		# ret += (' '* indent) + '\n'
		ret += (' '* indent) + '}\n'
		return ret	
	def __str__(self):
		return self.strIndent()