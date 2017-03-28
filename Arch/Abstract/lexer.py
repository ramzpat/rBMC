# abstract lexer
# asm_lexer.py
# ARM Unified Assembler Language

import ply.lex as lex
from abc import ABCMeta, abstractmethod

class ASMLex(object): 
  __metaclass__ = ABCMeta

  tokens = ['COMMENT',                      # Comments 
            'ASSERT', 'ASSUME',             # Annotations
            'REGISTER', 'NUMBER', 'COND',   # Reg, imm, assembly predicate
            'RELOP', 'BLIT','AND', 'OR', 'NOT',
            'ID'
            ]
  literals = [ '[', ']', ',', '#', ':', '(' ,')' ,]

  @abstractmethod
  def __init__(self):
    pass

  def lex(self, input):
    return self.lexer.input(input)

  # Build the lexer

  def build(self,**kwargs):
      self.lexer = lex.lex(module=self, **kwargs)

  # ----------- Lexer 
  # -- Annotations
  def t_ASSERT(self, t):
    r'assert | ASSERT'
    return t 
  def t_ASSUME(self, t):
    r'assume | ASSUME'
    return t
  def t_NOT(self, t):
    r'not'
    return t  
  def t_AND(self, t):
    r'and'
    return t
  def t_OR(self, t):
    r'or'
    return t
  # -- Boolean expressions' relation
  t_RELOP = r'<> | <= | >= | = | < | >'
  # -- Boolean constants 
  def t_BLIT(self, t):
    r'true | false'
    return t

  # -- Comment
  def t_COMMENT(self, t):
    r'\;[^\n]*'
    pass

  # -- Condition (Abstract)
  @abstractmethod 
  def t_COND(self, t):
    pass
  # -- Registers (Abstract)
  @abstractmethod
  def t_REGISTER(self, t):
    pass 

  # -- Identification
  def t_ID(self, t):
    r'[a-zA-Z_][a-zA-Z_0-9]*'
    # t.type = instr_tokens.get(t.value.lower(), 
    #             cond_tokens.get(t.value.lower(), 
    #                 'ID'))
    return t
    
  # -- Define a rule so we can track line numbers
  def t_newline(self, t):
        r'\n+'
        t.lexer.lineno += len(t.value)

  # A string containing ignored characters (spaces and tabs)
  t_ignore  = ' \t'

  # Error handling rule
  def t_error(self, t):
      print("Illegal character '%s'" % t.value[0])
      t.lexer.skip(1)



