import translator
import encoder 

from z3 import *
from HWModel.hw_z3 import *

def verify(P, arch = 'arm', model = 'SC', k = 0, debug = False):
	U = translator.translate(P, arch, k)
	j = 1
	result = unsat
	cModel = None
	cPrograms = None
	for u in U:
		# possible sets of programs 
		norm = encoder.normalize(u)
		
		if debug:
			print '========== [ Test set #%02d ] ==========='%(j)
			k = 0
			for p in norm:
				# a program in a set 
				print '====== Threadc #%d'%(k)
				for i in p:
					# each instruction
					print i
				k = k+1
			print '======================================='
		
		# Encoder ---------------- 
		(info,axioms) = encoder.archEncode(u,arch, model)

		# Verifier 
		s = Solver()
		s.add(axioms)

	  	result = s.check()

	  	if result == sat:
	  		cModel = s.model()
	  		cPrograms = norm
	  		break
	  	j = j + 1
	return (result, info, cPrograms, cModel)



    
def counter_example(cPrograms, info, model):

	procs = info['Proc']

	print '================= Nomalize Programs ======================'
	k = 0
	for p in cPrograms:
		# a program in a set 
		print '====== Thread #%d'%(k)
		for i in p:
			# each instruction
			print i
		k = k+1

	print '================= Memory operations ======================'
	
	for i in procs:
		print '==== Memory operations on Proc %2s'%i
		if len(info['counterExample']['read']) > 0:
			print '> Reads:'
		for (r, assn, p) in info['counterExample']['read']:
			if eq(p,i):
				print '  "%7s" \t represents \t "%10s"'%(r,assn)
		if len(info['counterExample']['write']) > 0:
			print '> Writes:'
		for (w, assn, p) in info['counterExample']['write']:
			if eq(p,i):
				print '  "%7s" \t represents \t "%10s"'%(w,assn)
		if len(info['counterExample']['rmw']) > 0:
			print '> Read-modify-write:'
		for (rmw, assn, p) in info['counterExample']['rmw']:
			if eq(p,i):
				print '  "%7s" \t represents \t "%10s"'%(rmw,assn)

	print '================= Trace ======================'

	def sort(array, order):
	    less = []
	    equal = []
	    greater = []

	    if len(array) > 1:
	        pivot = array[0]
	        for x in array:
	        	if eq(x,pivot):
	           		equal.append(x)
	           	elif is_true(order(x,pivot)):
	           		less.append(x)
		       	else:
					greater.append(x)
	        # Don't forget to return something!
	        return sort(less, order)+equal+sort(greater, order)  # Just use the + operator to join lists
	    # Note that you want equal ^^^^^ not pivot
	    else:  # You need to hande the part at the end of the recursion - when you only have one element in your array, just return the array.
	        return array

	def compare(x,y):
		return (model.evaluate(xo(x,y)))

	for i in procs:
		print '==== Trace on processor %s'%i
		ops = []
		for (r, assn, p) in info['counterExample']['read']:
			if eq(p, i):
				ops += [ subOpr(r, i) ]
		for (w, assn, p) in info['counterExample']['write']:
			ops += [ subOpr(w, i) ]
		for (a, assn, p) in info['counterExample']['rmw']:
			if eq(p, i):
				ops += [ subOpr(atomic_read(a), i) ]
			ops += [ subOpr(atomic_write(a), i) ]
		# if eq(i,procs[1]):
		print sort(ops, compare)

	return  

def counterTSO():
	P1 = '''
	mov r1, #1
	str r1, [X]
	ldr r2, [X]
	ldr r3, [Y]
	;assume( r2 = #1 )
	assert( r3 = #1 )
	'''

	P2 = '''
	mov r1, #1
	str r1, [Y]
	ldr r4, [Y]
	ldr r5, [X]
	;assume( r4 = #1 )
	assume( r5 = #0 )
	'''

	for cmodel in ["SC","TSO+"]:
		(result, info, programs, model) = verify([P1, P2], 'arm', cmodel)
		print "%s under %s"%("OK" if (result != sat) else "Not OK",cmodel)
		if result == sat:
			counter_example(programs, info, model)

def MessagePassing():
	P1 = '''
	mov r1, #1
	str r1, [X]
	str r1, [Y]
	'''

	P2 = '''
	L1: 
		ldr r1, [Y]
		cmp r1, #1
		bne L1
	ldr r2, [X]
	assert(r2 = #1)
	'''
	for cmodel in ["SC","TSO+", "PSO+"]:
		(result, info, programs, model) = verify([P1, P2], 'arm', cmodel)
		print "%s under %s"%("OK" if (result != sat) else "Not OK",cmodel)
		if result == sat:
			counter_example(programs, info, model)
			# brceak

def spinlock_sparc():
	# static inline void arch_spin_lock(arch_spinlock_t *lock)
	# {
	# 	unsigned long tmp;

	# 	__asm__ __volatile__(
	# "1:	ldstub		[%1], %0\n"
	# "	brnz,pn		%0, 2f\n" // 47		00101111
	# "	 nop\n"
	# "	.subsection	2\n"
	# "2:	ldub		[%1], %0\n"
	# "	brnz,pt		%0, 2b\n" //43		00101011
	# "	 nop\n"
	# "	ba,a,pt		%%xcc, 1b\n" //27   	00011011
	# "	.previous"
	# 	: "=&r" (tmp)
	# 	: "r" (lock)
	# 	: "memory");
	# }
	P1 = '''
	L1: 
	  ldstub [lock], r0
	  brnz,pn r0, L2
	  nop
	  ba L3
	  nop
	L2: 
	  ldub [lock], r1
	  brnz,pt r1, L2
	  nop 
	  ba,a,pt L1
	  nop
	L3:
	assume(r0 = #1)
	; critical
	'''
	P2 = '''
	L1: 
	  ldstub [lock], r0
	  brnz,pn r0, L2
	  nop
	  ba L3
	L2: 
	  ldub [lock], r1
	  brnz,pt r1, L2
	  nop 
	  ba,a,pt L1
	  nop
	L3:
	assert(r0 = #1)
	; critical
	'''
	for cmodel in ["SC","TSO+", "PSO+"]:
		# print cmodel
		(result, info, programs, model) = verify([P1, P2], 'sparc', cmodel, 0)
		print "%s under %s"%("OK" if (result != sat) else "Not OK",cmodel)
		if result == sat:
			counter_example(programs, info, model)

def checkTSOSpin():

	P1 = '''
	;critical
	mov r1, #0
	str r1, [X]
	'''
	P2 = '''
	  ldstub [lock], r0
	  
	'''
	for cmodel in ["SC","TSO+", "PSO+"]:
		# print cmodel
		(result, info, programs, model) = verify([P1, P2], 'sparc', cmodel, 0)
		print "%s under %s"%("OK" if (result != sat) else "Not OK",cmodel)
		if result == sat:
			counter_example(programs, info, model)

def JavaPSOerror():
	# Maximal Casuality Reduction for TSO and PSO 
	# T1:
	# z=0
	# x=0
	# y=0
	# x=2
	# y=3
	# z=1

	# T2:
	# if(z == 1)
	# 	if(x+1 != y)
	# 		print (x,y)

	P1 = '''
	mov r1, #0
	mov r2, #1
	mov r3, #2
	mov r4, #3
	str r1, [z]
	str r1, [x]
	str r1, [y]
	str r3, [x]
	str r4, [y]
	str r2, [z]
	'''

	P2 = '''
	ldr r1, [z]
	assume(r1 = #1)
	ldr r2, [x]
	ldr r3, [y]
	assert(r2 = #2 and r3 = #3)
	'''

	for cmodel in ["SC","TSO+", "PSO+"]:
		# print cmodel
		(result, info, programs, model) = verify([P1, P2], 'arm', cmodel, 0)
		print "%s under %s"%("OK" if (result != sat) else "Not OK",cmodel)
		if result == sat:
			counter_example(programs, info, model)

def dekker():
	# https://en.wikipedia.org/wiki/Dekker's_algorithm
	# p0:
 #   wants_to_enter[0] <- true
 #   while wants_to_enter[1] {
 #      if turn != 0 {
 #         wants_to_enter[0] <-false
 #         while turn != 0 {
 #           // busy wait
 #         }
 #         wants_to_enter[0] <- true
 #      }
 #   }

 #   // critical section
 #   ...
 #   turn <- 1
 #   wants_to_enter[0] <- false
 #   // remainder section

 # p1:
 #   wants_to_enter[1] <- true
 #   while wants_to_enter[0] {
 #      if turn != 1 {
 #         wants_to_enter[1] <- false
 #         while turn != 1 {
 #           // busy wait
 #         }
 #         wants_to_enter[1] <- true
 #      }
 #   }
 
 #   // critical section
 #   ...
 #   turn <- 0
 #   wants_to_enter[1] <- false
 #   // remainder section

 	dekker_prog_i = '''
	Lock: 
	mov r1, #1		; true
	mov r2, #0		; false
	mov r5, #2		; j
	str r1, [xi]	; x[i] = true
	While: 			; while(x[j]){
	ldr r3, [xj]	; 	x[j] (load to r3)
	cmp r3, #1		; 	x[j] = true ?
	assume(r3 <> #1)	; assume HERE*********
	bne CS			; 	!(x[j] = true) -> goto critical section
	If: 			; 	if( k == j(#2) )
	ldr r4, [k]		; 		k (load to r4)
	cmp r4, r5		;		k = j ?
	bne While  		; 		!(k = j) -> goto While
	str r2, [xi]	;		x[i] = false
	While2:			; 		while( k == j); ?
	ldr r4, [k]		;			k (load to r4)
	cmp	r4, r5		;			k = j ?
	beq While2		;			(k = 2) -> goto While2
	str r1, [xi]	;		x[i] = true
	b While 		; 	goto While
	CS:				; critical section:
	'''

	dekker_prog_j = '''
	Lock: 
	mov r1, #1		; true
	mov r2, #0		; false
	mov r5, #1		; i
	str r1, [xj]	; x[j] = true
	While: 			; while(x[j]){
	ldr r3, [xi]	; 	x[i] (load to r3)
	cmp r3, #1		; 	x[i] = true ?
	bne CS			; 	!(x[i] = true) -> goto critical section
	If: 			; 	if( k == i(#1) )
	ldr r4, [k]		; 		k (load to r4)
	cmp r4, r5		;		k = j ?
	bne While  		; 		!(k = i) -> goto While
	str r2, [xj]	;		x[j] = false
	While2:			; 		while( k == i); ?
	ldr r4, [k]		;			k (load to r4)
	cmp	r4, r5		;			k = i ?
	beq While2		;			(k = 1) -> goto While2
	str r1, [xj]	;		x[j] = true
	b While 		; 	goto While
	CS:				; critical section:
	assert(r3 = #1)
	'''

	for cmodel in ["SC","TSO+", "PSO+"]:
		# print cmodel
		(result, info, programs, model) = verify([dekker_prog_i, dekker_prog_j], 'arm', cmodel, 0)
		print "%s under %s"%("OK" if (result != sat) else "Not OK",cmodel)
		if result == sat:
			counter_example(programs, info, model)
	pass 
def peterson():
	# https://en.wikipedia.org/wiki/Peterson%27s_algorithm
	# 	bool flag[2] = {false, false};
	# int turn;

	# P0:      flag[0] = true;
	# P0_gate: turn = 1;
	#          while (flag[1] && turn == 1)
	#          {
	#              // busy wait
	#          }
	#          // critical section
	#          ...
	#          // end of critical section
	#          flag[0] = false;

	# P1:      flag[1] = true;
	# P1_gate: turn = 0;
	#          while (flag[0] && turn == 0)
	#          {
	#              // busy wait
	#          }
	#          // critical section
	#          ...
	#          // end of critical section
	#          flag[1] = false;

	P0 = '''
	mov r6, #0
	mov r1, #1
	str r1, [f0]	; flag[0] <- true
	P0_gate:
	str r1, [turn] 
	while:
	ldr r2, [f1] 
	cmp r2, #1
	bne CS
	while2:
	ldr r3, [turn]
	cmp r3, r1
	beq while
	CS: assume( r2 <> #1 or r3 <> r1 )
	unlock: 
	;str r6, [f0]
	'''

	P1 = '''
	mov r6, #0
	mov r1, #1
	str r1, [f1]	; flag[1] <- true
	P1_gate:
		str r6, [turn] 
	while:
		ldr r2, [f0] 
		cmp r2, #1
		bne CS
	while2:
		ldr r3, [turn]
		cmp r3, r6
		beq while
	CS: assert(not(r2 <> #1 or r3 <> r6))
	unlock: 
		;str r6, [f1]
	'''

	for cmodel in ["SC","TSO+", "PSO+"]:
		print 'process '+ str(cmodel)
		(result, info, programs, model) = verify([P0,P1], 'arm', cmodel, 0)
		print "%s under %s"%("OK" if (result != sat) else "Not OK",cmodel)
		if result == sat:
			counter_example(programs, info, model)
	pass 


# if __name__ == '__main__':	
# 	dekker()
# 	# peterson()

# 	# counterTSO()
# 	# MessagePassing()
# 	# spinlock_sparc()
# 	# JavaPSOerror()
# 	# print "\033[13m"

# 	# x = Int('x')
# 	# y = Int('y')

# 	# s = Solver()
	

# 	# s.add(x > 10, y == x + 2)
# 	# s.check()
# 	# print len(s.assertions())





	


