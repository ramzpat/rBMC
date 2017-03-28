

if __package__ is None:	
    import sys
    from os import path
    sys.path.append( path.dirname(path.dirname( path.dirname( path.abspath(__file__) ) ) ))
    from Arch.Abstract.semantics import constructCFG as semanticsARM
else:
	from Arch.Abstract.semantics import constructCFG as semanticsARM
