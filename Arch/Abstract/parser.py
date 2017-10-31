# asm_parser.py
# Yacc example

import ply.yacc as yacc

# Get the token map from the lexer.  This is required.
# from asm_lexer import lexer, tokens, literals

if __package__ is None:
    import sys
    from os import path
    sys.path.append( path.dirname(path.dirname( path.dirname( path.abspath(__file__) ) ) ))
    from Arch.objects import *
else:
	from Arch.objects import *

from z3 import *
from abc import ABCMeta, abstractmethod

class ASMParser(object):
  	__metaclass__ = ABCMeta
	
	def __init__(self, tokens, literals):
		self.tokens = tokens
		self.literals = literals
		self.build()

	# -- Program def 
	@abstractmethod
	def p_program_statements(self, p):
		'''
		program : statements
		'''
		p[0] = p[1]

	@abstractmethod
	def p_statements(self, p):
		'''
		statements : statement 
					| statement statements
		'''
		if(len(p) == 2):
			p[0] = p[1]
		else:
			p[0] = p[1] + p[2]

	@abstractmethod
	def p_statement(self, p):
		'''
		statement : 	ID ':' 
					|	ID ':' instruction
					| instruction
		'''
		if len(p) == 3:
			p[0] = [(label(p[1]))]
		elif len(p) == 4:
			p[0] = [(label(p[1])), (p[3])]
		else: 
			p[0] = [p[1]]

	@abstractmethod
	def p_instruction(self, p):
		pass 

	def p_instruction_nop(self, p):
		'''
		instruction : NOP
		'''
		p[0] = [InstrOps(Operation())]

	def p_instruction_assert(self, p):
		'''
		instruction : ASSERT '(' bexp ')'
		'''
		p[0] = [Assertion(p[3])]
	def p_instruction_assume(self, p):
		'''
		instruction : ASSUME '(' bexp ')'
		'''
		p[0] = [Assume(p[3])]
	def p_instruction_do(self, p):
		'''
		instruction : DO '{' statements '{' bexp '}' '}' WHILE '(' bexp ')' 
		'''
		# p[0] = 
		p[0] = [DoWhile( SeqOps(*p[3]), p[5], p[10])]

	def p_instruction_if(self, p):
		'''
		instruction : IF '(' bexp ')' '{' statements '}' 
		'''
		p[0] = [IfBr( p[3], SeqOps(*p[6]) ) ]

	def p_instruction_assn(self, p):
		'''
		instruction : '$' ID ':' RELOP exp
		'''
		if(p[4] == '='):
			p[0] = [SeqOps(AuxVar(p[2]) << p[5])]
		# p[0] = 

	# ------------ ASSERT
	def p_exp(self, p):
		'''
		exp : texp '+' texp 
			| texp '-' texp
			| texp
		'''
		if len(p) == 2:
			p[0] = p[1]
		elif p[2] == '+':
			p[0] = p[1] + p[3]
		else:
			p[0] = p[1] - p[3] 
			# p[0] = Exp(p[1], p[2], p[3])
	def p_texp(self, p):
		'''
		texp : factor '*' factor 
			 | factor '/' factor
			 | factor
		'''
		if(len(p) == 2):
			p[0] = p[1]
		elif p[2] == '*':
			p[0] = p[1] * p[3]
		else:
			p[0] = p[1] / p[2]
			# p[0] = Exp(p[1], p[2], p[3])
	def p_factor_exp(self, p):
		'''
		factor : '(' exp ')'
		'''
		p[0] = p[2]
	def p_factor_operand(self, p):
		'''
		factor : operand
		'''
		p[0] = p[1]

	def p_factor_aux(self, p):
		'''
		factor : '$' ID 
		'''
		p[0] = AuxVar(p[2])

	def p_bexp(self, p):
		'''
		bexp : bterm 
			 | bexp OR bterm
		'''
		if len(p) == 2:
			p[0] = p[1]
		else:
			p[0] = (p[1] | p[3])
		
	def p_bterm_nfactor(self, p):
		'bterm : nfactor'
		p[0] = p[1]
	def p_bterm_nfactor_and(self, p):
		'bterm : nfactor AND bterm'
		p[0] = (p[1] & p[3])
	def p_nfactor_not(self, p):
		'nfactor : NOT bfactor '
		p[0] = not(p[2])
	def p_nfactor_bfactor(self, p):
		'nfactor : bfactor '
		p[0] = (p[1])

	def p_bfactor_brelation(self, p):
		'''
		bfactor : brelation
		'''
		p[0] = p[1]

	def p_bfactor(self, p):
		'''
		bfactor : BLIT
				| '(' bexp ')'
		'''
		if p[1] == 'true':
			p[0] = (True)
			
		elif p[1] == 'false':
			p[0] = (False)
		elif len(p) > 2:
			p[0] = p[2]


	def p_brelation(self, p):
		'''
		brelation : exp RELOP exp
		'''
		#  t_RELOP = r'<> | <= | >= | = | < | >'
		
		if p[2] == '<>':
			p[0] = p[1] != p[3]
		elif p[2] == '<=':
			p[0] = p[1] <= p[3]
		elif p[2] == '>=':
			p[0] = p[1] >= p[3]
		elif p[2] == '=':
			p[0] = p[1] == p[3]
		elif p[2] == '<':
			p[0] = p[1] < p[3]
		else:
			p[0] = p[1] > p[3]
		# print (p[0])

		# p[0] = Exp(p[1], p[2], p[3])


	# Error rule for syntax errors
	def p_error(self, p):
	    print("Syntax error in input!")

	def build(self):
		self.parser = yacc.yacc(module = self, errorlog=yacc.NullLogger())
		# self.parser = yacc.yacc(module = self)

# Build the parser
# p = ARMParser().parser
# parser = yacc.yacc()
