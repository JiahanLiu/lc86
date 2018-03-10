# on OSX
# gcc -m32 test_and_to_not.S -o test_and_to_not
# objdump -d test_and_to_not
# made in loving memory of the numbers 4, 2, 0

.data
hello:
	.string "Hello world!\n"
.text
.globl _main
_main:
		#ADD
		add $1, %al #op 04
		add $0x04444, %ax #op 05, operand override
		add $0x0fffffffffffffff, %eax #op 05 
		add $0x22, %bl #op 80, register
		addb $0x01, -0x20(%ebx, %ecx, 0x4) #op80 memory
		add $0x0fff, %sp #op81, operand override, register
		addw $0x0abc, 0x0bfa(%eax, %ebx, 0x8) #op81, operand override, memory
		add $0x1024, %ebp #op81, register
		addl $0x4200, 0x0faa(%ecx, %eax, 0x2)#op81, memory
		add $0x2, %ax #op83, operand override, register
		addw $0x8, 0x01fa(%eax, %ebx, 0x8) #op83, operand override, memory
		add $0x2, %eax #op83, register
		addl $0x8, 0x0f2a(%eax, %ebx, 0x4) #op83, memory
		add %dh, %ah #op00, register
		add %dh, 0x03fa(%eax, %ebx, 0x1) #op00, memory
		add %bp, %cx #op01, operand override, register
		add %ax, 0x04fa(%eax, %ebx, 0x8) #op01, operand override, memory
		add %ebp, %ecx #op01, register
		add %ecx, 0x05fa(%eax, %ebx, 0x1) #op01, memory
		add %dl, %bl #op02, register,
		add 0x0f6a(%eax, %ebx, 0x8), %bl #op02, memory
		add %di, %si #op03, operand override, register
		add 0x1ffa(%eax, %ebx, 0x2), %sp #op03, operand override, memory
		add %edi, %esi #op03, register
		add 0x2ffa(%eax, %ebx, 0x8), %eax #op03, memory
myfunc0:
		#AND
		and $1, %al #op 24
		and $0x0fff, %ax #op 25, operand override
		and $0x0fffffffffffffff, %eax #op 25 
		and $0x24, %bl #op 80, register
		andb $0xff, -0x20(%ebx, %ebx, 0x4) #op 80 memory
		and $0x0204, %sp #op 81, operand override, register
		andw $0x0abc, 0x2ffa(%eax, %ebx, 0x8) #op 81, operand override, memory
		and $0x1234, %ebp #op 81, register
		andl $0x0abc, 0x9ffa(%ecx, %eax, 0x1)#op 81, memory
		and $0x2, %ax #op 83, operand override, register
		andw $0x8, 0x1ffa(%eax, %ebx, 0x8) #op 83, operand override, memory
		and $0x2, %eax #op 83, register
		andl $0x8, 0x3ffa(%eax, %ebx, 0x2) #op 83, memory
		and %dh, %ah #op 20, register
		and %dh, 0x0aaa(%eax, %ebx, 0x8) #op 20, memory
		and %bp, %cx #op 21, operand override, register
		and %ax, 0x0bba(%eax, %ebx, 0x1) #op 21, operand override, memory
		and %ebp, %ecx #op 21, register
		and %ecx, 0x0c9a(%eax, %ebx, 0x8) #op 21, memory
		and %dl, %bl #op 22, register,
		and 0x0420(%eax, %eax, 0x4), %bl #op 22, memory
		and %di, %si #op 23, operand override, register
		and 0x0024(%eax, %ebx, 0x4), %sp #op 23, operand override, memory
		and %edi, %esi #op 23, register
		and 0x0420(%eax, %ebx, 0x4), %eax #op 23, memory

		#call
		call myfunc0 #op e8, operand overwrite
		call myfunc0 #op e8
		call *%ax #op ff, operand override, register
		callw *0x4222(%eax, %ebx, 0x4) #op ff, operand override, memory
		call *%ebx #op ff, register
		call *0x4220(%eax, %ebx, 0x4) #op 9a, memory

		#cld
		cld #op fc

		#cmov
		cmovc %ax, %bx#op 0f 42, operand override, register
		cmovc 0x420a(%eax, %ebx, 0x4), %ax #op 0f 42, operand override, memory
		cmovc %eax, %ecx #op 0f 42, register
		cmovc 0x04260(%eax, %ebx, 0x4), %edx #op 0f 42, memory

		#cmpxchg
		cmpxchg %al, %cl #op 0f b0, register
		cmpxchg %al, 0x1444(%ebx, %ebx, 0x4) #op 0f b0, memory
		cmpxchg %ax, %bx #op 0f b1, operand override, register
		cmpxchg %ax, 0x2222(%ebx, %ebx, 0x2) #op 0f b1, operand override, memory
		cmpxchg %eax, %ebx #op 0f b1, register
		cmpxchg %eax, 0x3000(%ebx, %ebx, 0x1) #op 0f b1, memory

		#daa
		daa #op 27

		#hlt
		hlt #op f4

		#inc
		inc %ch #op fe, register
		incb 0x1444(%ebx) #op fe, memory
		inc %si #op ff, operand override, register
		incw 0x4240(%ebx, %eax, 0x1) #op ff, operand override, memory
		inc %eax #op ff, register
		incl 0x4204(%ebx, %eax, 0x1) #op ff, memory
		inc %si #op 40
		inc %ebx #op 41

myfunc1:
		#iret
		iret

		#jcc
		jnbe myfunc1 #op 77
		jne myfunc1 #op 75
		jnbe myfunc0 #op 0f 87, operand override
		jnbe myfunc0 #op 0f 87
		jne myfunc0 #op 0f 85
		jne myfunc0 #op 0f 85, operand override

		#jmp
		jmp myfunc1 #op eb
		jmp myfunc0 #op e9, operand override
		jmp *0x04200420 #op e9
		jmp *%ax #op ff, operand override, register
		jmpw *0x4204(%eax, %eax, 0x8) #op ff, operand override, memory
		jmp *%bx #op ff, register
		jmpl *0x4204(%eax, %eax, 0x8) #op ff, memory
		jmpw $0x4444,$0x2222 #op ea, pointer16:16
		jmpl $0x4444,$0x22220000#op ea, pointer16:32

		#mov
		mov $1, %al #op 88
		mov $0x0fff, %ax #op 89, operand override
		mov $0x0fffffffffffffff, %eax #op 89 
		mov $0x24, %bl #op 8a, register
		movb $0xff, -0x20(%ebx, %ebx, 0x4) #op 8a memory
		mov $0x0204, %sp #op 8a, operand override, register
		movw $0x0abc, 0x2ffa(%eax, %ebx, 0x8) #op 8a, operand override, memory
		mov $0x1234, %ebp #op 8b, register
		movl $0x0abc, 0x9ffa(%ecx, %eax, 0x1)#op 8b, memory
		mov $0x2, %ax #op 8b, operand override, register
		movw $0x8, 0x1ffa(%eax, %ebx, 0x8) #op 8b, operand override, memory
		mov $0x2, %eax #op 8c, register
		movl $0x8, 0x3ffa(%eax, %ebx, 0x2) #op 8c, memory
		mov %dh, %ah #op B0, register
		mov %dh, 0x0aaa(%eax, %ebx, 0x8) #op B0, memory
		mov %bp, %cx #op B8, operand override, register
		mov %ax, 0x0bba(%eax, %ebx, 0x1) #op B8, operand override, memory
		mov %ebp, %ecx #op B8, register
		mov %ecx, 0x0c9a(%eax, %ebx, 0x8) #op B8, memory
		mov %dl, %bl #op C6, register,
		mov 0x0420(%eax, %eax, 0x4), %bl #op C6, memory
		mov %di, %si #op C7, operand override, register
		mov 0x0024(%eax, %ebx, 0x4), %sp #op C7, operand override, memory
		mov %edi, %esi #op C7, register
		mov 0x0420(%eax, %ebx, 0x4), %eax #op C7, memory






