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


def z3Instr(instr, info):

	CS = [] # Programs behaviors (Not accumulate)
	PS = [] # Programs Properties (Not accumulate)
	Regs = info['Regs']	# Register (accumulate)

	if isinstance(instr, InstrAssert):
		PS += [z3Exp(instr.cond, info)]
	elif isinstance(instr, InstrAssume):
		CS += [z3Exp(instr.cond, info)]
	elif isinstance(instr, i_assignment):
		Regs[str(instr.var)] = Int(str(instr.var)) 
		var = Regs[str(instr.var)]
		exp = instr.expression
		if isinstance(exp, i_read):
			# New read 
			name = 'read_'+str(info['ReadCnt'])
			info['ReadCnt'] = info['ReadCnt'] + 1			
			read = Const(name,hw.ReadOp)							# Generate a fresh memory operation (read operation)

			info['counterExample']['read'] += [(read, instr, info['Proc'][-1])]

			addr = str(exp.opr)
			info['Loc'][addr] = Const(addr, hw.Loc)

			loc = info['Loc'][addr]

			info['MemOp']['read'] += [(read, loc, info['Proc'][-1])]	# Add the memory operation
			info['po'] = info['po']	+ [read]							# Update the program order

			CS = [var == hw.return_val(read),
				  hw.mem_access(read) == loc, 
				  hw.issue_proc(read) == info['Proc'][-1]
				  ]
		elif isinstance(exp, i_rmw):
			# New rmw 
			name = 'rmw_'+str(info['RmwCnt'])
			info['RmwCnt'] = info['RmwCnt'] + 1
			rmw = Const(name, hw.AtomicOp)							# Generate a fresh memory operation (rmw operation)

			info['counterExample']['rmw'] += [(rmw, instr, info['Proc'][-1])]

			addr = str(exp.addr)
			info['Loc'][addr] = Const(addr, hw.Loc)
			loc = info['Loc'][addr]

			info['MemOp']['rmw'] += [(rmw, loc, info['Proc'][-1])]		# Add the memory operation
			info['po'] = info['po']	+ [rmw] 							# Update the program order 

			write_val = Regs[str(exp.rt)] if isinstance(exp.rt, Register) else exp.rt

			CS = [ 	var == hw.return_val(hw.atomic_read(rmw)),
					hw.mem_access(hw.atomic_read(rmw)) == loc,
					hw.mem_access(hw.atomic_write(rmw)) == loc, 
					hw.issue_proc(hw.atomic_read(rmw)) == info['Proc'][-1], 
					hw.issue_proc(hw.atomic_write(rmw)) == info['Proc'][-1],
					hw.write_val(hw.atomic_write(rmw)) == write_val
			]
		elif isinstance(exp, i_if_exp):

			t_exp = (var == If( z3Exp(exp.cond, info),  
							z3Exp(exp.t_exp, info), z3Exp(exp.f_exp, info)))
			# f_exp = Implies( Not(z3_exp(r.cond, Regs)),  
							# Regs[str(e.var)] == z3_exp(r.f_exp, Regs))
			# (e_cs, new_ps, Regs, Wop, Rop, RMWop, Ls, po) = self.statement_behav_z3(s[1:], Regs, Wop, Rop, RMWop, Ls, Proc)
			CS = [ t_exp ]
		else: 
			CS += [ var == z3Exp(instr.expression, info) ]
	elif isinstance(instr, i_write):
		# New write
		name = 'write_' + str(info['WriteCnt'])
		info['WriteCnt'] = info['WriteCnt'] + 1
		write = Const(name, hw.WriteOp)								# Generate a fresh memory operation (write operation)

		info['counterExample']['write'] += [(write, instr, info['Proc'][-1])]

		addr = str(instr.addr)
		info['Loc'][addr] = Const(addr, hw.Loc)
		loc = info['Loc'][addr]

		info['MemOp']['write'] += [(write, loc, info['Proc'][-1])]		# Add the memory operation
		info['po'] = info['po'] + [write]

		CS = [	hw.write_val(write) == Regs[str(instr.rt)],
				hw.mem_access(write) == loc, hw.issue_proc(write) == info['Proc'][-1]
				]
	elif isinstance(instr, i_if):
		cs = []
		infoS = info
		for s in instr.statement:
			infoS = z3Instr(s, infoS)
		cs = infoS['CS']
		ps = info['PS'] 

		cond = (z3Exp(instr.cond, info))

		newCS = [Implies(cond, cc) for cc in cs]
		newPS = [Implies(cond, cc) for cc in ps]
	
		CS += newCS
		PS += newPS

	info['CS'] = CS 
	info['PS'] = PS
	info['Regs'] = Regs
	return info

def encode(listS):
	info = {
		'CS' : [],			# Program Behaviors
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

	# (1) Encode instructions as program behaviors (CS)
	# (2) Collect Memory Operations 
	# (4) Program Properties (PS)
	CS = []
	PS = []
	PO = []
	p = 0
	for s in listS:
		info['Proc'] += [Const('P'+str(p), hw.Proc)]
		info['po'] = []
		for e in s:
			info = z3Instr(e, info)
			CS += info['CS']
			PS += info['PS']

		# (2.5) Generate the program order of program s 
		po_z3 = []
		o = info['po']
		PO += [info['po']]
		if(len(o) >= 2):
			for i in range(1,len(o)):
				po_z3 += [hw.po(o[i-1], o[i])]
		CS += po_z3
		p = p + 1

	# Each location should different
	for (l1, l2) in itertools.combinations(info['Loc'],2):
		CS += [ Not(info['Loc'][l1] == info['Loc'][l2]) ]
		

	info['CS'] = CS
	info['PS'] = PS
	info['po'] = PO

	# (3) Generate conditions for CS 
	
	return info