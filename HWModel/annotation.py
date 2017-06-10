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

class DoWhile(AnnotatedStatement):
	def __init__(self, body, inv, branchInstr, Q):
		self.body = body 			# loop body
		self.bInstr = branchInstr 	# branch condition
		self.inv = inv 				# invariant
		self.Q = Q					# post-condition

	def strIndent(self, indent = 0):
		ret = ''
		ret += (' '* indent) + '{ \n'
		ret += str(self.body.strIndent(indent + 1))
		# ret += (' '* indent) + '\n'
		ret += (' '* indent) + '{ '+ str(self.inv) +' }\n'
		ret += (' '* indent) + '}while('+ str(self.bInstr) +')' + '\n'
		ret += (' '* indent) + '{ '+ str(self.Q) +' }\n'
		return ret

	def __str__(self):
		return self.strIndent()