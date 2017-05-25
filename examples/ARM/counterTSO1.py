mov r1, #1
str r1, [X]
ldr r2, [X]
ldr r3, [Y]
;assume( r2 = #1 )
assert( r3 = #1 )