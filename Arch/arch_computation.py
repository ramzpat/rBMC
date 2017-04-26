# arch_computation

from arch_object import *

# =========== CFG Definition =========== 
# Represent instructions / operators
class node(): 
	pred = [] 
	def __init__(self, obj, *link):
		self.obj = obj 
		self.link = link 
		self.pred = []
	def __str__(self):
		return 'node(' + str(self.obj)+ ')'
	def addLink(self, *link):
		self.link += link 
	def setLink(self, *link):
		self.link = link 
	def next(self):
		return self.link

class CFGNode(node):
	isLoop = False 

	def nextSeq(self):
		(cond, nextSq) = self.next()[0]
		return nextSq 
	def branch(self):
		(cond, nextSq) = self.next()[1]
		return nextSq 

	cdList = None 
	def cd(self):
		return []

	def __iter__(self):
		node = self 
		while node:
			yield node
	   		node = node.nextSeq()

# Utilities methods for constructing CFG
def getBranch(instr):
	if isinstance(instr, Instr) and instr.is_branch:

		cond = instr.operands[0]
		label = instr.operands[1]
		return (cond, label)
	if isinstance(instr, InstrBranch):
		return (instr.condition(), instr.targetLabel())
	else:
		return None  
def getLabel(l):
	if isinstance(l, Label):
		return l
	else:
		return None
def isLoop(node , cfg):
	for e in cfg:
		if(e == node):
			return True
	return False

