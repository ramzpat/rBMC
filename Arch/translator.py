

# from ARMParser import parser as arm_parser
from objects import *
# from Abstract.semantics import *

# ARM
if __package__ is None:
	import sys
	from os import path
	sys.path.append( (path.dirname( path.dirname( path.abspath(__file__) ) ) ))
	import ARM.parser as arm_parser
	from ARM.lexer import lexer as armLexer
else:
	import ARM.parser as arm_parser
	from ARM.lexer import lexer as armLexer

# from Arch.ARM.arm_object import *
# from Arch.ARM.semantics import semanticsARM as arm_cfg, getARMSemantics

# SPARC
# import Arch.SPARC.parser as sparc_parser 
# from Arch.SPARC.lexer import lexer as sparcLexer 
# from Arch.SPARC.semantics import constructSPARCCGF as sparc_cfg


# ========================== Parser 
__current_parser = None
__parser_list = ['arm', 'sparc']
__parser_obj = None 

# Return a list of exist parsers
def parsers():
	return __parser_list

def getLexer():
	if __current_parser == 'arm':
		return armLexer
	elif __current_parser == 'sparc':
		return sparcLexer
	return None

def __parserObj(p):
	parser = None 
	if p == 'arm':
		parser = arm_parser.ARMParser().parser
	elif p == 'sparc':
		parser = sparc_parser.SPARCParser().parser
	return parser

# (1) Parse each p in a list of programs, P
# Parse asm programs w/ it's syntax architecture
# Return the set of <arch-object> list that can be used in python programs 
def parse(s, parser = 'arm'):
	global __current_parser
	global __parser_obj
	if __current_parser != parser:
		__parser_obj = __parserObj(parser)
		__current_parser = parser

	if isinstance(s, list):
		newS = []
		for e in s:
			newS += [parse(e, parser)]
		return newS
	else:
		return __parser_obj.parse(s, lexer = getLexer())

# construct a CFG from a list of <arch-object> w/ it's syntax archtecture
def constructCFG(P, arch):
	# (2) Construct CFG(s)
	cfg = []
	if arch == 'sparc':
		for p in P:
			cfg += [sparc_cfg(p)]
	else:
		for p in P:
			cfg += [arm_cfg(p)]
	return cfg 


# =================================== Unroll
def exploreExecution(U):
	if len(U) >= 1:
		E = []
		for (e, info) in U[0]:
			# print e[]
			E += [e]
		for es in exploreExecution(U[1:]):
			for e in E:
				yield [e] + es
	else: 
		yield []

# Unroll the cfg with a k-bound 
#  -------- new unroll
def unroll(cfg, k = 0):
	U = []
  	for c in cfg:
  		U += [unrollSeq(c.nextSeq(), k)]
  	return exploreExecution(U)

def unrollSeq(cfg, k = 0):
	c = cfg
	poInstr = []
	# pDom = postDominateAnalysis(cfg)
	pDom = None
	for (e,info) in __unroll(c, {'k':k, 'poInstr':poInstr, 'pDom':pDom}):
		poInstr = info['poInstr']
		cd = []
		# for i in range(0,len(e)):
		# 	for j in range(i+1,len(e)):
		# 		if not(e[j].parent in pDom[e[i].parent]):
		# 			cd += [(e[i], e[j])]
		# info['cd'] = cd
		yield (e,info)

def __unroll(cfg, info):
	# Travel along the tree
	k = info['k']
	e = cfg 
	if e:
		# Label
		if(getLabel(e.obj) != None):	# Eliminate Label
			for (e1,info) in __unroll( e.nextSeq(), info):
				yield (e1,info)
		# Branch
		elif( getBranch(e.obj) != None ):
			(tAssume, fAssume) = e.obj.unroll()
			t_assert = tAssume #[instr_assume(e.link_cond)]
			for es in tAssume:
				es.parent = e 
			for es in fAssume:
				es.parent = e 
			info['poInstr'] += [e]
			if(e.isLoop and k > 0 ):
				for (e1,info) in __unroll( e.nextSeq(), info):
					f_assert = fAssume 
					yield (f_assert + e1, info)
				info2 = info
				info2['k'] = k - 1
				for (e1,info) in __unroll( e.branch(), info2):
					yield (t_assert + e1, info)
			elif(not(e.isLoop)):
				for (e1, info) in __unroll( e.nextSeq(),info):
					f_assert = fAssume 
					yield (f_assert + e1, info)
				for (e1, info) in __unroll( e.branch(), info):
					yield (t_assert + e1, info)
			else:
				for (e1,info) in __unroll( e.nextSeq(), info):
					f_assert = fAssume 
					yield (f_assert + e1, info)
		else: # Instr
			info2 = info
			# Consider instruction(Instr)
			if isinstance(e.obj, Instr):		
				info2['poInstr'] = info['poInstr'] + [e]
			for (e1,info) in __unroll( e.nextSeq(), info):
				if isinstance(e.obj, Instr):
					new_seq = e.obj.iSemantics()
					for es in new_seq:
						es.parent = e
				else: 
					new_seq = []
				yield (new_seq + e1, info2)
	else :
		yield ([], info)
	

# =================== Translator
def translate(P, arch = 'arm'):
	# parsing 
	result = parse(P, arch)
	# CFG constructing 
	if not isinstance(P, list):
		result = [result]
	# cfg = constructCFG(result, arch)
	# Unrolling 
	# U = unroll(cfg, k)
	return result

def justParse(P, arch = 'arm'):
	# parsing 
	result = parse(P, arch)
	# CFG constructing 
	if not isinstance(P, list):
		result = [result]
	cfg = constructCFG(result, arch)
	return cfg 

# For test this translator 
if __name__ == "__main__":
	arm_prog = '''
	mov r1, #1
	mov r4, #2
	str r1, [X]
	str r4, [C]
	ldr r2, [C]
	ldr r3, [A]
	assert(r2 = #2)
	assert(r3 = #1)
	'''

	U = translate(arm_prog)
	# j = 1
	# for u in U:
	# 	# possible sets of programs 
	# 	print '========== [ Test set #%02d ] ==========='%(j)
	# 	k = 0
	# 	for p in u:
	# 		# a program in a set 
	# 		print '====== Thread #%d'%(k)
	# 		for i in p:
	# 			# each instruction
	# 			print i
	# 		k = k+1
	# 	j = j + 1
	
	# print '========== branch test ======'
	# arm_prog = '''
	# L1:
	# mov r1, #1
	# mov r4, #2
	# b L1
	# '''
	# U = justParse(arm_prog)
	# k = 0
	# for p in U:
	# 	# a program in a set 
	# 	print '====== Thread #%d'%(k)
	# 	for i in p:
	# 		# each instruction
	# 		print i
	# 	k = k+1
	# U = translate(arm_prog, k = 2)
	# j = 1
	# for u in U:
	# 	# possible sets of programs 
	# 	print '========== [ Test set #%02d ] ==========='%(j)
	# 	k = 0
	# 	for p in u:
	# 		# a program in a set 
	# 		print '====== Thread #%d'%(k)
	# 		for i in p:
	# 			# each instruction
	# 			print i
	# 		k = k+1
	# 	j = j + 1


	# P1 = '''
	# L1:
	# 	ldstub	[lock], r0
	# 	brnz,pn r0, L2
	# 	nop
	# 	ba,a CS ;subsection -> previous
	# 	nop
	# L2:
	# 	ldub [lock], r0
	# 	brnz,pt r0, L2
	# 	nop
	# 	ba,a,pt L1
	# CS:	
	# ; critical section
	# '''
	# # result = parse(P1, 'sparc')
	# # if not isinstance(P1, list):
	# # 	result = [result]
	# # cfg = constructCFG(result, 'sparc')
	
	# U = justParse(P1, 'sparc')
	# k = 0
	# for p in U:
	# 	# a program in a set 
	# 	print '====== Thread #%d'%(k)
	# 	for i in p:
	# 		# each instruction
	# 		print i
	# 	k = k+1
	
	# p = [
	# Label('L'),
	# ARMInstr(ARMInstr.ldr, ARMCond.al, ARMReg.r2, Location(ARMReg.r1)),
	# ARMInstr(ARMInstr.mov, ARMCond.al, ARMReg.r3, Location(ARMReg.r2)), 
	# ARMInstr(ARMInstr.b, ARMCond.eq, Label('L'))
	# ]
	# cfg = arm_cfg(p)
	# for n in cfg.nextSeq():
	# 	print n


	# U = unroll([cfg], 1)
	# for u in U:
	# 	print '-----'
	# 	for p in u:
	# 		for i in p:
	# 			print i


	pass