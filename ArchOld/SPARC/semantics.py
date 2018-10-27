if __package__ is None:
    import sys
    from os import path
    sys.path.append( path.dirname(path.dirname( path.dirname( path.abspath(__file__) ) ) ))
    from Arch.arch_computation import *
else:
	from Arch.arch_computation import *

# SPARC CFG for delayed instructions
def constructSPARCCGF(s):
	cfg = CFGNode(s[len(s)-1], (True,None))

	# Construct CFG
	for i in range(len(s)-1,0, -1):
		new_node = CFGNode(s[i-1], (True, cfg))
		cfg.pred += new_node
		cfg = new_node

	start = CFGNode('start', (True, cfg))
	cfg.pred = [start]
	# start.pred = []

	# Link branch conditions
	for node in start.nextSeq(): 
		if( getBranch(node.obj) != None  ):
			(cond, bLink) = getBranch(node.obj)
			aBit = node.obj.annul
			for l in start.nextSeq():
				if( getLabel(l.obj) == bLink ):
					if(aBit and cond == True):
						nextNode = node.nextSeq()
						falsePath = nextNode.nextSeq()
						nextNode.setLink((True, l))
						node.setLink( 	(False, falsePath),
										(True, nextNode))
					elif (aBit):
						nextNode = node.nextSeq()
						falsePath = nextNode.nextSeq()
						nextNode.setLink((True, l))
						node.setLink(	(Exp(EOpr['not'], cond), falsePath), 
										(cond, nextNode))
					else:		

						nextNode = node.nextSeq()
						newNode = CFGNode(nextNode.obj, (True, l))
						node.setLink(	( Exp(EOpr['not'], cond), node.nextSeq()), 
										(cond, newNode))

					node.isLoop = isLoop(node, l)
					l.pred += node 
					break 
	return start 