from z3 import *
# Additional Op
MembarWR =	DeclareSort('MEMBAR(WR)')				# MEMBER(WR) operation in TSO+ (spac v8+) 
STBar = DeclareSort('STBar')