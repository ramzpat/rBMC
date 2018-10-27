
if __package__ is None:
	import sys
	from os import path
	sys.path.append( path.dirname(( path.dirname( path.abspath(__file__) ) ) ))
	from Modules.Ops.objects import *
else:
	from Modules.Ops.objects import *

# from objects import *

if __name__ == '__main__':
	P1 = seqOpsNode(
			InstrOps(	# mov r1, #1
				TempReg('val') << 1,
				AuxVar('cnt') << TempReg('val'), 
				Register('r1') << TempReg('val')
				),
			InstrOps(	# str r1, [x]
				TempReg('val') << Register('r1'),
				Location('x') << TempReg('val')
				),
			InstrOps(	# str r1, [y]
				TempReg('val') << Register('r1'),
				Location('y') << TempReg('val')
			))
	
	for e in P1:
		print e