.data
hello:
	.string "Hello world!\n"
.text
.globl _main
_main:
	#ADD
	add $1, %al #op 04
	add $0x0fff, %ax #op 05, operand override
	add $0x0fffffffffffffff, %eax #op 05 
	add $0xff, %bl #op 80, register
	addb $0xff, -0x20(%ebx, %ecx, 0x4) #op80 memory
	add $0x0fff, %sp #op81, operand override, register
	addw $0x0abc, 0x0ffa(%eax, %ebx, 0x8) #op81, operand override, memory
	add $0x1234, %ebp #op81, register
	addl $0x0abc, 0x0ffa(%ecx, %eax, 0x2)#op81, memory
	add $0x2, %ax #op83, operand override, register
	addw $0x8, 0x0ffa(%eax, %ebx, 0x8) #op83, operand override, memory
	add $0x2, %eax #op83, register
	addl $0x8, 0x0ffa(%eax, %ebx, 0x4) #op83, memory
	add %dh, %ah #op00, register
	add %dh, 0x0ffa(%eax, %ebx, 0x1) #op00, memory
	add %bp, %cx #op01, operand override, register
	add %ax, 0x0ffa(%eax, %ebx, 0x8) #op01, operand override, memory
	add %ebp, %ecx #op01, register
	add %ecx, 0x0ffa(%eax, %ebx, 0x1) #op01, memory
	add %dl, %bl #op02, register,
	add 0x0ffa(%eax, %ebx, 0x8), %bl #op02, memory
	add %di, %si #op03, operand override, register
	add 0x0ffa(%eax, %ebx, 0x2), %sp #op03, operand override, memory
	add %edi, %esi #op03, register
	add 0x0ffa(%eax, %ebx, 0x8), %eax #op03, memory

	#AND
	and $1, %al #op 24
	and $0x0fff, %ax #op 25, operand override
	and $0x0fffffffffffffff, %eax #op 25 
	and $0xff, %bl #op 80, register
	andb $0xff, -0x20(%ebx, %ecx, 0x4) #op 80 memory
	and $0x0fff, %sp #op 81, operand override, register
	andw $0x0abc, 0x0ffa(%eax, %ebx, 0x8) #op 81, operand override, memory
	and $0x1234, %ebp #op 81, register
	andl $0x0abc, 0x0ffa(%ecx, %eax, 0x1)#op 81, memory
	and $0x2, %ax #op 83, operand override, register
	andw $0x8, 0x0ffa(%eax, %ebx, 0x8) #op 83, operand override, memory
	and $0x2, %eax #op 83, register
	andl $0x8, 0x0ffa(%eax, %ebx, 0x2) #op 83, memory
	and %dh, %ah #op 20, register
	and %dh, 0x0ffa(%eax, %ebx, 0x8) #op 20, memory
	and %bp, %cx #op 21, operand override, register
	and %ax, 0x0ffa(%eax, %ebx, 0x1) #op 21, operand override, memory
	and %ebp, %ecx #op 21, register
	and %ecx, 0x0ffa(%eax, %ebx, 0x8) #op 21, memory
	and %dl, %bl #op 22, register,
	and 0x0ffa(%eax, %ebx, 0x4), %bl #op 22, memory
	and %di, %si #op 23, operand override, register
	and 0x0ffa(%eax, %ebx, 0x4), %sp #op 23, operand override, memory
	and %edi, %esi #op 23, register
	and 0x0ffa(%eax, %ebx, 0x4), %eax #op 23, memory

	

