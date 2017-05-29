# Encode
# Z3 Solver with HW model
from z3 import *
import itertools

if __package__ is None:
    import sys
    from os import path
    sys.path.append( (path.dirname( path.dirname( path.abspath(__file__) ) ) ))
    from Arch.arch_object import *
    import hw_z3 as hw
else:
	from Arch.arch_object import *
	import hw_z3 as hw

def z3Exp(exp, info):
	# print exp
	if isinstance(exp, Register):
		if str(exp) in info['Regs']:			
			return info['Regs'][str(exp)]
		else:
			info['Regs'][str(exp)] = Int(str(exp))
			return info['Regs'][str(exp)] 
	elif isinstance(exp, int):
		return exp
	elif isinstance(exp, bool):
		return exp
	elif isinstance(exp, Exp):
		if(len(exp) > 2):
			op = exp[1]
			if op == EOpr['plus']:
				return z3Exp(exp[0], info) + z3Exp(exp[2], info)
			elif op == EOpr['minus']:
				return z3Exp(exp[0], info) - z3Exp(exp[2], info)
			elif op == EOpr['times']:
				return z3Exp(exp[0], info) * z3Exp(exp[2], info)
			elif op == EOpr['divide']:
				return z3Exp(exp[0], info) / z3Exp(exp[2], info)
			elif op == EOpr['eq']:
				return (z3Exp(exp[0], info) == z3Exp(exp[2], info))
			elif op == EOpr['lt']:
				return z3Exp(exp[0], info) < z3Exp(exp[2], info)
			elif op == EOpr['gt']:
				return z3Exp(exp[0], info) > z3Exp(exp[2], info)
			elif op == EOpr['and']:
				return And(z3Exp(exp[0], info),z3Exp(exp[2], info))
			elif op == EOpr['or']:
				return Or(z3Exp(exp[0], info),z3Exp(exp[2], info))
		elif len(exp) == 2:
			if exp[0] == EOpr['not']:
				return Not(z3Exp(exp[1], info))
		else:
			return z3Exp(exp[0], info)
	return False


# translation of a statement (intermediate representation)
def z3Instr(instr, info):

	CS = [] 	# Programs behaviors (Not accumulate)
	InfoS = [] 	# Program information
	BasisS = []	# Behavior property 

	PS = [] # Programs Properties (Not accumulate)
	Regs = info['Regs']	# Register (accumulate)

	# translation of assertion
	if isinstance(instr, InstrAssert):
		PS += [z3Exp(instr.cond, info)]

	# translation of assertion
	elif isinstance(instr, InstrAssume):
		# CS += [z3Exp(instr.cond, info)]
		InfoS += [z3Exp(instr.cond, info)]

	# translation of assingment
	elif isinstance(instr, i_assignment):
		Regs[str(instr.var)] = Int(str(instr.var)) 
		var = Regs[str(instr.var)]
		exp = instr.expression

		# the assignment read a shared-memory location
		if isinstance(exp, i_read):
			# New read 
			name = 'read_'+str(info['ReadCnt'])
			info['ReadCnt'] = info['ReadCnt'] + 1			
			read = Const(name,hw.ReadOp)							# Generate a fresh memory operation (read operation)

			# collect data for presenting a counterexample 
			info['counterExample']['read'] += [(read, instr, info['Proc'][-1])]

			addr = str(exp.opr)
			info['Loc'][addr] = Const(addr, hw.Loc)
			loc = info['Loc'][addr]
			# read \in R_S
			info['MemOp']['read'] += [(read, loc, info['Proc'][-1])]	# Add the memory operation
			info['po'] = info['po']	+ [read]							# Update the program order

			# transformation of read
			InfoS += [var == hw.return_val(read),
				  hw.mem_access(read) == loc, 
				  hw.issue_proc(read) == info['Proc'][-1]
				  ]

		# the assignment read a value from rmw statement
		elif isinstance(exp, i_rmw):

			# New rmw 
			# name = 'rmw_'+str(info['RmwCnt'])
			# info['RmwCnt'] = info['RmwCnt'] + 1
			# rmw = Const(name, hw.AtomicOp)							# Generate a fresh memory operation (rmw operation)

			read = Const('read_'+str(info['ReadCnt']), hw.ReadOp)
			write = Const('write_'+str(info['WriteCnt']), hw.WriteOp)
			info['ReadCnt'] = info['ReadCnt'] + 1			
			info['WriteCnt'] = info['WriteCnt'] + 1

			# collect data for presenting a counterexample 
			info['counterExample']['read'] += [(read, instr, info['Proc'][-1])]
			info['counterExample']['write'] += [(write, instr, info['Proc'][-1])]
			# info['counterExample']['rmw'] += [ (rmw, instr, info['Proc'][-1]) ]

			addr = str(exp.addr)
			info['Loc'][addr] = Const(addr, hw.Loc)
			loc = info['Loc'][addr]

			# r, w \in RW_S
			info['MemOp']['read'] += [(read, loc, info['Proc'][-1])]	# Add the memory operation
			info['MemOp']['write'] += [(write, loc, info['Proc'][-1])]	# Add the memory operation
			info['MemOp']['rmw'] += [((read, loc, info['Proc'][-1]), (write, loc, info['Proc'][-1]))]		# Add the read-modify-write behavior
			info['po'] = info['po'] + [read, write]						# Update the program order 
			# info['po'] = info['po']	+ [rmw] 							# Update the program order 

			write_val = Regs[str(exp.rt)] if isinstance(exp.rt, Register) else exp.rt

			# transformation of rmw
			InfoS += [
					# read
					var == hw.return_val(read),
					hw.mem_access(read) == loc,
					hw.issue_proc(read) == info['Proc'][-1],
					# write
					hw.write_val(write) == write_val,
					hw.mem_access(write)== loc,
					hw.issue_proc(write) == info['Proc'][-1]

					# var == hw.return_val(hw.atomic_read(rmw)),
					# hw.mem_access(hw.atomic_read(rmw)) == loc,
					# hw.mem_access(hw.atomic_write(rmw)) == loc, 
					# hw.issue_proc(hw.atomic_read(rmw)) == info['Proc'][-1], 
					# hw.issue_proc(hw.atomic_write(rmw)) == info['Proc'][-1],
					# hw.write_val(hw.atomic_write(rmw)) == write_val
			]

		# the result from if-expression ( in the form (cond)? exp1:exp2 )
		elif isinstance(exp, i_if_exp):

			t_exp = (var == If( z3Exp(exp.cond, info),  
							z3Exp(exp.t_exp, info), z3Exp(exp.f_exp, info)))
			# f_exp = Implies( Not(z3_exp(r.cond, Regs)),  
							# Regs[str(e.var)] == z3_exp(r.f_exp, Regs))
			# (e_cs, new_ps, Regs, Wop, Rop, RMWop, Ls, po) = self.statement_behav_z3(s[1:], Regs, Wop, Rop, RMWop, Ls, Proc)

			# transformation of read
			InfoS += [ t_exp ]

		# normal expression
		else: 
			InfoS += [ var == z3Exp(instr.expression, info) ]

	# translation of write statement
	elif isinstance(instr, i_write):
		# New write
		name = 'write_' + str(info['WriteCnt'])
		info['WriteCnt'] = info['WriteCnt'] + 1
		write = Const(name, hw.WriteOp)								# Generate a fresh memory operation (write operation)

		info['counterExample']['write'] += [(write, instr, info['Proc'][-1])]

		addr = str(instr.addr)
		info['Loc'][addr] = Const(addr, hw.Loc)
		loc = info['Loc'][addr]

		# write \in W_S
		info['MemOp']['write'] += [(write, loc, info['Proc'][-1])]		# Add the memory operation
		info['po'] = info['po'] + [write]

		InfoS = [	hw.write_val(write) == Regs[str(instr.rt)],
				hw.mem_access(write) == loc, hw.issue_proc(write) == info['Proc'][-1]
				]

	# translation of if statement
	elif isinstance(instr, i_if):
		info2 = info
		for s in instr.statement:
			info2 = z3Instr(s, info2)
		ifs = info2['InfoS']
		ps = info['PS'] 

		cond = (z3Exp(instr.cond, info))

		newInfoS = [Implies(cond, cc) for cc in ifs]
		newPS = [Implies(cond, cc) for cc in ps]
	
		InfoS += newInfoS
		PS += newPS

	# info['CS'] = CS 
	info['InfoS'] = InfoS 
	info['PS'] = PS
	info['Regs'] = Regs
	return info

def encode(listS):
	info = {
		'CS' : [],			# Program Behaviors
			'InfoS': [],	# Program Information
			'BasisS':[],	# Behavior property
		'PS' : [],			# Program Properties
		'MemOp' : {			# Memory Operations
			'write':[], 	#  - Write Operations 				(name, accessLocation, issuedProc)
			'read':[], 		#  - Read Operations				(name, accessLocation, issuedProc)
			'rmw':[],		#  - Read-modify-write Operations 	(name, accessLocation, issuedProc)
			'special':[]	# special instructions 
			},		
		'po' : [],			# Program Order
		'Regs' : {},			# A set of registers 

		'ReadCnt' : 0,
		'WriteCnt' : 0,
		'RmwCnt' : 0,

		'Loc' : {}, 	# A set of locations
		'Proc' : [],
		'spo' : [],
		'sco' : [],

		'counterExample' :{	# Counter example information
				'read' : [],
				'write' : [],
				'rmw' : [],
				'special' : [],
			}
	}

	# (1) Encode instructions as program information (InfoS)
	# (2) Collect Memory Operations 
	# (4) Program Properties (PS)
	InfoS = []
	BasisS = []
	PS = []
	PO = []
	p = 0
	for s in listS:
		info['Proc'] += [Const('P'+str(p), hw.Proc)]
		info['po'] = []
		for e in s:
			info = z3Instr(e, info)
			InfoS += info['InfoS']
			PS += info['PS']

		# (2.5) Generate the program order of program s 
		po_z3 = []
		o = info['po']
		PO += [info['po']]
		if(len(o) >= 2):
			for i in range(1,len(o)):
				po_z3 += [hw.po(o[i-1], o[i])]
		InfoS += po_z3
		p = p + 1

	# Each location should different
	for (l1, l2) in itertools.combinations(info['Loc'],2):
		BasisS += [ Not(info['Loc'][l1] == info['Loc'][l2]) ]
		

	info['InfoS'] = InfoS 
	info['BasisS'] = BasisS
	info['CS'] = InfoS + BasisS
	info['PS'] = PS
	info['po'] = PO

	# (3) Generate conditions for CS 
	
	return info