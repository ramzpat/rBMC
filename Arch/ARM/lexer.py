# ARM lexer# Lexer for ARM architecture
# arm_lexer.py

import ply.lex as lex
   
# from asm_lexer import ASMLex
if __package__ is None:
  import sys
  from os import path
  sys.path.append( path.dirname(path.dirname( path.dirname( path.abspath(__file__) ) ) ))
  from Arch.Abstract.lexer import ASMLex
else:
  from Arch.Abstract.lexer import ASMLex

class ARMLex(ASMLex):

  tokens = ['INSTR1', 'INSTR2', 'INSTR_SWP', 'INSTR_BRANCH']   
  literals = []

  def __init__(self):
    self.tokens = self.tokens + super(ARMLex, self).tokens
    self.literals = self.literals + super(ARMLex, self).literals
    self.build()
  
  t_NUMBER = r'[0-9]+'
  def t_INSTR1(self, t):
    r'mov | MOV | sub | SUB | add | ADD | cmp | CMP '
    return t
  def t_INSTR2(self, t):
    r'str | STR | ldr | LDR '
    return t
  def t_INSTR_SWP(self, t):
    r'swp | SWP'
    return t 
  def t_INSTR_BRANCH(self, t):
    r'b | B'
    return t

  # -- Concrete lexers 
  def t_COND(self, t):
    r'eq | EQ | ne | NE'
    return t
  
  def t_REGISTER(self, t):
    r'r[0-9]+ | pc | lr | sp '
    return t

# # Build 
lex = ARMLex()
lexer = lex.lexer
tokens = lex.tokens
literals = lex.literals

if __name__ == '__main__':
  # # Test it out
  data = '''
    L:  mov r1, #1
        SWP r1, r2, [A]
        CMP r1, #1
        STR EQ r1, [A]
        assert([A] = r1)
    '''
  data = '''
  do{
  ldr r1, [y]
  cmp r1, #1
  }while(n = 1)
  assert([x] = #1)
  '''
  lexer.input(data)

  while True:
      tok = lexer.token()
      if not tok: 
          break      # No more input
      print(tok)

# m_prog = '''
# mov r1, #1
# str r1, [X]
# str r1, [Y]
# L:
# ldr r1, [Y]
# cmp r1, #1
# beq L
# ldr r2, [X]
# '''
