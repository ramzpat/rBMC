if __package__ is None:
    import sys
    from os import path
    sys.path.append( path.dirname( path.dirname( path.abspath(__file__) ) ) )
    from Arch.arch_computation import *
else:
	from Arch.arch_computation import *

def fenceList():
	return []

# Standard CFG for asm behaviors 
def constructCFG(s):	
	cfg = CFGNode(s[len(s)-1], (True,None))

	# Construct CFG
	for i in range(len(s)-1,0, -1):
		new_node = CFGNode(s[i-1], (True, cfg))
		cfg.pred += new_node 
		cfg = new_node

	start = CFGNode('start', (True, cfg))
	
	# Link branch conditions
	for node in start.nextSeq(): 
		if( getBranch(node.obj) != None  ):
			(cond, bLink) = getBranch(node.obj)
			for l in start.nextSeq():
				if( getLabel(l.obj) == bLink ):
					node.setLink(( Exp(EOpr['not'], cond), node.nextSeq()), (cond, l))
					node.isLoop = isLoop(node, l)
					l.pred = node
					break 
	return start 