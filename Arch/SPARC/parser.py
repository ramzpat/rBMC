# Sparc parser

# asm_parser.py
# Yacc example

import ply.yacc as yacc


# External Package
if __package__ is None:
  import sys
  from os import path
  sys.path.append( path.dirname(path.dirname( path.dirname( path.abspath(__file__) ) ) ))
  from Arch.Abstract.parser import ASMParser
else:
  from Arch.Abstract.parser import ASMParser

# Get the token map from the lexer.  This is required.
from lexer import lexer as plexer, tokens as ptokens, literals as pliterals
from sparc_object import *
# from z3 import *


class SPARCParser(ASMParser):
	def __init__(self, tokens = ptokens, literals = pliterals):
		self.tokens = tokens
		self.literals = literals
		self.build()
		
	def p_program_statements(self, p):
		'''
		program : statements
		'''
		p[0] = (p[1])
	def p_statements(self, p):
		'''
		statements : statement 
					| statement statements
		'''
		if(len(p) == 2):
			p[0] = p[1]
		else:
			p[0] = p[1] + p[2]
	def p_statement(self, p):
		'''
		statement : 	ID ':' 
					|	ID ':' instruction
					| instruction
		'''
		if len(p) == 3:
			p[0] = [(Label(p[1]))]
		elif len(p) == 4:
			p[0] = [(Label(p[1]))] + p[3]
		else: 
			p[0] = p[1]

	def p_instruction(self, p):
		''' instruction : instr_processing
						| instr_atomic
						| instr_memwr
						| instr_memory
						| instr_branch
						| instr_branch_a
						| instr_mov 
		'''
		p[0] = p[1]

	def p_instruction_instr_nop(self, p):
		''' instruction : INSTR_NOP
		'''
		p[0] = [None]

	def p_instr_memwr(self, p):
		'''	instr_memwr : MEM_SYNC '#' MEM_MASK
		'''
		p[0] = instr_fence(p[3])

	def p_instr_processing(self, p):
		''' instr_processing : INSTR_ARTH REGISTER ',' operand
		'''
		p[0] = instr(p[1], [Register(p[2]), p[4]])

	def p_instr_mov(self, p):
		''' instr_mov : INSTR_MOVE operand ',' REGISTER
		'''
		p[0] = instr(p[1], [p[2],Register(p[4])])

	def p_instr_memory_instr_st(self, p):
		''' instr_memory : INSTR_ST '[' ID ']' ',' REGISTER  
		'''
		p[0] = instr_memory(p[1], p[3] , Register(p[6]))

	def p_instr_memory_instr_ld(self, p):
		''' instr_memory : INSTR_LD '[' ID ']' ',' REGISTER  
		'''
		p[0] = instr_memory(p[1], p[3] , Register(p[6]))

	def p_instr_atomic_instr_atm(self, p):
		''' instr_atomic : INSTR_ATM '[' ID ']' ',' REGISTER  
		'''
		p[0] = instr_memory(p[1], p[3] , Register(p[6]))
	def p_instr_branch(self, p):
		''' instr_branch : cti_instr REGISTER ',' ID 
		'''
		p[0] = instr_branch(p[1], Register(p[2]), p[4])


	def p_instr_branch_a(self, p):
		''' instr_branch_a : cti_a_instr ID 
		'''
		p[0] = instr_branch(p[1], Register('-'), p[2])

	def p_cti_instr(self, p):
		''' cti_instr : INSTR_BRANCH ',' ID ',' ID
					  | INSTR_BRANCH ',' ID 
					  | INSTR_BRANCH
		'''
		if len(p) == 6:
			p[0] = [p[1], p[3], p[5]]
		elif len(p) == 4:
			p[0] = [p[1], (p[3])]
		else:
			p[0] = [p[1]]


	def p_cti_a_instr(self, p):
		''' cti_a_instr : INSTR_BRANCH_A ',' ID ',' ID
					  | INSTR_BRANCH_A ',' ID 
					  | INSTR_BRANCH_A
		'''
		if len(p) == 6:
			p[0] = [p[1], p[3], p[5]]
		elif len(p) == 4:
			p[0] = [p[1], (p[3])]
		else:
			p[0] = [p[1]]

	def p_operands_operand(self, p):
		'''operands : '#' NUMBER'''
		p[0] = [int(p[2])]
	def p_operands_register(self, p):
		'''operands : REGISTER'''
		p[0] = [Register(p[1])]

	def p_operands_operand_operands(self, p):
		'''operands : operand ',' operands'''
		p[0] = [p[1]] + p[3]

	def p_operand_number(self, p):
		'''operand : '#' NUMBER'''
		p[0] = int(p[2])

	def p_operand_register(self, p):
		'operand : REGISTER'
		p[0] = Register(p[1])

# if __name__ == '__main__':
# 	ss = '''
# 	L1: 
# 	  ldstub [lock], r0
# 	  brnz,pn r0, L2
# 	  nop
# 	  ba L3
# 	  nop
# 	L2: 
# 	  ldub [lock], r1
# 	  brnz,pt r1, L2
# 	  nop 
# 	  ba,a,pt L1
# 	  nop
# 	L3:
# 	; critical
# 	'''

# 	parser = SPARCParser().parser
# 	# print '====='
# 	result = parser.parse(ss)
# 	# print result
# 	for e in result:
# 		print e
