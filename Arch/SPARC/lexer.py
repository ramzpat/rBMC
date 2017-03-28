# lexer
import ply.lex as lex

if __package__ is None:
  import sys
  from os import path
  sys.path.append( path.dirname(path.dirname( path.dirname( path.abspath(__file__) ) ) ))
  from Arch.Abstract.lexer import ASMLex
else:
  from Arch.Abstract.lexer import ASMLex

# Instructions fall into the following basic categories: 
# - Memory access
# - Integer operate
# - Control transfer
# - State register access
# - Floating-point operate
# - Conditional move
# - Register window management

# Instruction
# ADD, ADDcc, AND, 
# BPcc, Bicc, BPr
# LDD, LDDA, LDUB, LDSTUB
# MOVcc, MOVr
# MEMBAR, STBAR
# STD
# SUB



class SPARCLex(ASMLex):

  tokens = [
            # Memory Access
            'INSTR_LD', # Load
            'INSTR_ST',  # Store
            'INSTR_ATM', # Atomic
            'MEM_SYNC', # Memory Synchronization
            # Arithmetic/Logical/Shift Instructions
            'INSTR_ARTH', 
            'INSTR_NOP', # No operation
            # Control Transfer
            # State Register Access
            'INSTR_MOVE',# Conditional Move

            'INSTR_BRANCH', # Branch
            'INSTR_BRANCH_A', # Branch Alway

            ]   
  literals = []

  def __init__(self):
    self.tokens = self.tokens + super(SPARCLex, self).tokens
    self.literals = self.literals + super(SPARCLex, self).literals
    self.build()
  
  t_NUMBER = r'[0-9]+'

  # -- Concrete lexers 

  def t_INSTR_NOP(self, t):
    r'nop'
    return t 

  def t_INSTR_BRANCH_A(self, t):
    r'ba'
    return t

  def t_INSTR_BRANCH(self, t):
    r'brz | brlez | brnz | brlz | brgz | brgez '
    return t

  def t_INSTR_MOVE(self, t):
    r'mova | movn | movne'
    return t 

  def t_INSTR_ATM(self, t):
    r'ldstub | swp | casxa | casa'
    return t 
    
  def t_INSTR_LD(self, t):
    r'ldub | ld'
    return t
  def t_REGISTER(self, t):
    r'r[0-9]+ | pc | npc '
    return t

  def t_COND(self, t):
    r'eq | EQ | ne | NE'
    return t
  



  def t_INSTR_ARTH(self, t):
    r'add '
    return t 

  def t_INSTR_ST(self, t):
    r'stub | st'
    return t
  def t_MEM_SYNC(self, t):
    r'FLUSH | MEMBAR' 
    return t 
   # -- Identification
  def t_ID(self, t):
    r'[a-zA-Z_][a-zA-Z_0-9]*'
    # t.type = instr_tokens.get(t.value.lower(), 
    #             cond_tokens.get(t.value.lower(), 
    #                 'ID'))
    return t




  

# Build 
lex = SPARCLex()
lexer = lex.lexer
tokens = lex.tokens

literals = lex.literals

# Test it out
# %0 : &tmp
# %1 : lock
s = '''
L1: 
  ldstub [lock], r0
  brnz,pn tmp, L2
  ba L3:
L2: 
  ldub [lock], r1
  brnz,pt r1, L2
  nop 
  ba,a,pt L1
L3:
'''

ss = '''
L2: 
  ldub [lock], r1
  brnz,pt r1, L2
  nop 
  ba,a,pt L1
L3:
'''


# lexer.input(s)
# while True:
#     tok = lexer.token()
#     if not tok: 
#         break      # No more input
#     print(tok)
