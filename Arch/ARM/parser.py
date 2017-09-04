# the parser for ARM syntax
# asm_parser.py
# Yacc example

import ply.yacc as yacc

# Get the token map from the lexer.  This is required.
# from arm_lexer import lexer as arm_lexer, tokens as arm_tokens, literals as arm_literals
# from asm_parser import ASMParser
from arm_object import *

# External Package
if __package__ is None:
  import sys
  from os import path
  sys.path.append( path.dirname(path.dirname( path.dirname( path.abspath(__file__) ) ) ))
  from Arch.Abstract.parser import ASMParser
  # from Arch.objects import *
else:
  from Arch.Abstract.parser import ASMParser
  # from Arch.objects import *

from lexer import lexer as arm_lexer, tokens as arm_tokens, literals as arm_literals




class ARMParser(ASMParser):

	def __init__(self, tokens = arm_tokens, literals = arm_literals):
		self.tokens = tokens
		self.literals = literals
		self.build()


	def p_program_statements(self, p):
		'''
		program : statements
		'''
		p[0] = seqOpsNode(*p[1])

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
						| instr_memory 
						| instr_swp 
						| instr_branch
		'''
		p[0] = p[1]

	def p_instr_processing(self, p):
		''' instr_processing : INSTR1 COND REGISTER ',' operand 
				  | INSTR1 REGISTER ',' operand
		'''
		if len(p) == 5 :
			p[0] = instr(p[1], [Register(p[2]), p[4]])
		else:
			p[0] = instr(p[1], [Register(p[3]), p[5]], cond = (p[2]))

	def p_instr_memory(self, p):
		''' instr_memory : INSTR2 COND REGISTER ',' '[' ID ']'
				  | INSTR2 REGISTER ',' '[' ID ']'
		'''
		if len(p) == 7 :
			# print str(p.lineno(1)) + " : " + str(p[1])
			p[0] = instr_memory(p[1], Register(p[2]), p[5])
		else:
			p[0] = instr_memory(p[1], Register(p[3]), p[6], cond = (p[2]))
	def p_instr_swp(self, p):
		''' instr_swp 	: INSTR_SWP COND REGISTER ',' REGISTER ',' '[' ID ']'
					| INSTR_SWP REGISTER ',' REGISTER ',' '[' ID ']'
		'''
		if len(p) == 9 :
			p[0] = instr_swp(Register(p[2]), Register(p[4]), p[7])
		else:
			p[0] = instr_swp(Register(p[3]), Register(p[5]), p[8], cond = (p[2]))
	def p_instr_branch(self, p):
		''' instr_branch : INSTR_BRANCH COND ID
				  | INSTR_BRANCH ID 
		'''
		if len(p) > 3:
			p[0] = instr_branch(p[3], cond = (p[2]))
		else:
			p[0] = instr_branch(p[2])


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
	def p_operand_location(self, p):
		'''
		operand : '[' ID ']' 
		'''
		p[0] = Location(p[2])

# Build the parser
# parser = yacc.yacc()



# lexer = ARMLex().lexer
# parser = ARMParser(arm_tokens, arm_literals).parser

# Build the parser
# p = ARMParser().parser
# parser = yacc.yacc()

def parse(P):
	parser = ARMParser(arm_tokens, arm_literals).parser
	# parser = yacc.yacc()
	result = parser.parse(P)
	return result


if __name__ == '__main__':
	s = '''
	L1 : mov r1, r1 ; test
	mov r2, r1
	add r2, #2
	b eq L1
	ldr r1, [A]
	'''

	s_spin = '''
	Lock: 
	  mov r1, #1
	  swp r1, r1, [locked]
	  cmp r1, #1
	  beq Lock
	  ; critical section
	Unlock:
	  moveq r1, #0 
	  swp r1, r1, [locked]
	'''
	m_prog = '''
	Lock: 
	mov r1, #1 
	str r1, [A]
	str r1, [Y]
	assert([A] = #1)
	'''
	p = parse(m_prog)
	for i in p:
		print i
	pass



