# Annotation


class AnnotatedStatement():
	pass 

class Assertion(AnnotatedStatement):
	def __init__(self, cond):
		self.cond = cond
	def __str__(self):
		return 'assert(' + str(self.cond) + ')'

class Assume(AnnotatedStatement):
	def __init__(self, cond):
		self.cond = cond
	def __str__(self):
		return 'assume(' + str(self.cond) + ')'

# Havoc operator for inductive invariant
# havoc( {<var>}+ )
class havoc(AnnotatedStatement):
	def __init__(self, *v):
		self.vars = v
	def getVars(self):
		return self.vars
	def __str__(self):
		ret = 'havoc('
		ret += str(self.vars[0])
		for v in self.vars[1:]:
			ret += ', ' + str(v)
		return ret + ')'


class DoWhile(AnnotatedStatement):
	def __init__(self, body, inv, branchInstr, Q):
		self.body = body 			# loop body
		self.bInstr = branchInstr 	# branch condition
		self.inv = inv 				# invariant
		self.Q = Q					# post-condition

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