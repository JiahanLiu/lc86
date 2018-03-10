	.org 0x3000

	# opcode 0F 6F
	movq	(%esi), %mm0 #SIB and overrides
	movq	%mm1, (%edi)

	# opcode F2 A6
	repne cmpsb	%es:(%edi), %fs:(%esi)
	repne cmpsw	%es:(%edi), %ds:(%esi)
	repne cmpsw	%es:(%edi), %gs:(%esi)
	repne cmpsl	%es:(%edi), %fs:(%esi)

	# opcode F6
	notb	%ch
	notb	%fs:(%ecx, %edx, 1)
	notw	%cx
	notw	%ss:(%eax, %edx, 2)	
	notl	%edx
	notl	%gs:(%edx, %eax, 4)
	
	# opcodes 0C, OD
	or	$0x7F, %al
	or	$0x7FFF, %ax
	or	$0x7FFFFFFF, %eax

	# opcode 80
	orb	$0x0F, %dh 
	orb	$0x67, (%ebx)
	orb	$0x67, %es:(%ecx)

	orb	$0x62, -16(%ebx) 
	orb	$0x45, %gs:23(%ecx)
	
	orb	$0x12, 0x80000000(%esi)
	orb	$0x23, %fs:0x7ffeeeee(%edi)
	
	orb	$0x32, (0x3000)
	orb	$0x75, %gs:(0x3000)

	orb	$0x75, (%ebx, %ecx, 8)
	orb	$0x21, 0xF0(%ebx, %esi, 4)
	orb	$0x64, -0x332f1663(%eax, %ebp, 2)
	orb	$0x64, %es:-0x332f1663(%edi, %ebp, 2)
	
	# opcode 81, operand-override
	orw	$0x320F, %dx 
	orw	$0x2467, (%ebx)
	orw	$0x2467, %es:(%ecx)

	orw	$0x1362, -16(%ebx) 
	orw	$0xF245, %gs:23(%ecx)
	
	orw	$0x2312, 0x80000000(%esi)
	orw	$0x1823, %fs:0x7ffeeeee(%edi)
	
	orw	$0x8532, (0x3000)
	orw	$0x3275, %gs:(0x3000)

	orw	$0x2375, (%ebx, %ecx, 8)
	orw	$0x6221, 0xF0(%ebx, %esi, 4)
	orw	$0x7364, -0x332f1663(%eax, %ebp, 2)
	orw	$0x5664, %ds:-0x332f1663(%edi, %ebp, 1)
	
	# opcode 81
	orl	$0x320F, %edx 
	orl	$0x2467, (%ebx)
	orl	$0x2467, %es:(%ecx)

	orl	$0x1362, -16(%ebx) 
	orl	$0xF245, %gs:23(%ecx)
	
	orl	$0x2312, 0x80000000(%esi)
	orl	$0x1823, %fs:0x7ffeeeee(%edi)
	
	orl	$0x8532, (0x3000)
	orl	$0x3275, %gs:(0x3000)

	# opcode 83, operand-override
	orw	$0x0F, %bp 
	orw	$0x67, (%ebx)
	orw	$0x67, %es:(%esp)

	orw	$0x62, -16(%ebx) 
	orw	$0x45, %gs:23(%ecx)
	
	orw	$0x12, 0x80000000(%esi)
	orw	$0x23, %fs:0x7ffeeeee(%edi)
	
	orw	$0x32, (0x3000)
	orw	$0x75, %gs:(0x3000)

	# opcode 83
	orl	$0x0F, %ebp 
	orl	$0x67, (%ebx)
	orl	$0x67, %es:(%esp)

	orl	$0x62, -16(%ebx) 
	orl	$0x45, %gs:23(%ecx)
	
	orl	$0x12, 0x80000000(%esi)
	orl	$0x23, %fs:0x7ffeeeee(%edi)
	
	orl	$0x32, (0x3000)
	orl	$0x75, %gs:(0x3000)

	# opcode 08
	orb	%bh, %bl
	orb	%ah, (%ebx)
	orb	%dh, %cs:(%ebx)

	orb	%bl, -16(%ebx) 
	orb	%dl, %gs:23(%ecx)
	
	orb	%ch, 0x80000000(%esi)
	orb	%dh, %fs:0x7ffeeeee(%edi)
	
	orb	%ah, (0x3000)
	orb	%cl, %gs:(0x3000)

	# opcode 09, operand-override
	orw	%bx, %bp
	orw	%si, (%ebx)
	orw	%di, %cs:(%ebx)

	orw	%ax, -16(%ebx) 
	orw	%cx, %gs:23(%ecx)

	orw	%dx, 0x80000000(%esi)
	orw	%bx, %fs:0x7ffeeeee(%edi)
	
	orw	%sp, (0x3000)
	orw	%bp, %gs:(0x3000)

	# opcode 09
	orl	%ebx, %ebp
	orl	%esi, (%ebx)
	orl	%edi, %cs:(%ebx)

	orl	%eax, -16(%ebx) 
	orl	%ecx, %gs:23(%ecx)

	orl	%edx, 0x80000000(%esi)
	orl	%ebx, %fs:0x7ffeeeee(%edi)
	
	orl	%esp, (0x3000)
	orl	%ebp, %gs:(0x3000)

	# opcode 0A
	orb	%bh, %bl
	orb	(%ebx), %ah
	orb	%cs:(%ebx), %dh

	orb	-16(%ebx), %bl 
	orb	%gs:23(%ecx), %dl
	
	orb	0x80000000(%esi), %ch
	orb	%fs:0x7ffeeeee(%edi), %dh
	
	orb	(0x3000), %ah
	orb	%gs:(0x3000), %cl

	# opcode 0b, operand-override
	orw	%bp, %bx
	orw	(%ebx), %si
	orw	%cs:(%ebx), %di

	orw	-16(%ebx), %ax 
	orw	%gs:23(%ecx), %cx

	orw	0x80000000(%esi), %dx
	orw	%fs:0x7ffeeeee(%edi), %bx
	
	orw	(0x3000), %sp
	orw	%gs:(0x3000), %bp

	# opcode 0b
	orl	%ebp, %ebx
	orl	(%ebx), %esi
	orl	%cs:(%ebx), %edi

	orl	-16(%ebx), %eax 
	orl	%gs:23(%ecx), %ecx

	orl	0x80000000(%esi), %edx
	orl	%fs:0x7ffeeeee(%edi), %ebx
	
	orl	(0x3000), %esp
	orl	%gs:(0x3000), %ebp

	# opcode 0F FD
	paddw	%mm0, %mm1
	paddw	(%esp), %mm1
	paddw	%es:(%ebx), %mm2 
	paddw	-0x6322133F(%edx, %esi, 4), %mm2 

	paddd	%mm3, %mm1
	paddsw 	%mm7, %mm2

	# opcode 8F, operand-override
	popw	%dx
	popw	(%esi)
	popw	0x23(%edi)
	popw	0x3000
	popw	0x23963322(%esi)
	popw	%es:-0x6233(%esi, %edi, 2)

	# opcode 8F - must change stack pointer 
	popl	%edx
	popl	(%esi)
	popl	0x23(%edi)
	popl	0x3000
	popl	0x23963322(%esi)
	popl	%es:-0x6233(%esi, %edi, 2)

	pop	%ds
	pop	%es
	pop	%ss
	pop	%fs
	pop	%gs

	# opcode 0F 70
	pshufw	$0x08, %mm1, %mm7
	pshufw 	$0x55, (%ecx), %mm2
	pshufw	$0xEA, 0x632F1EAB(%esi, %ebp, 8), %mm3

	# opcode FF, operand-override
	pushw	(0x3000)
	pushw	%es:(%ebp) # need SIB

	# opcode FF
	pushl	%fs:(0x3000)

	# opcode 50+rw
	pushw	%sp
	pushl	%ebp

	# opcode 6A, 68
	push	$0x33
	pushw	$0x2435
	pushl	$0x42366334

	push	%cs
	push	%ss
	push	%ds
	push	%es
	push 	%fs
	push	%gs

	# opcode A6, A7
	cmpsb	%es:(%edi), %fs:(%esi)
	cmpsw	%es:(%edi), %ds:(%esi)
	cmpsw	%es:(%edi), %gs:(%esi)
	cmpsl	%es:(%edi), %fs:(%esi)

	# opcode C3 
	ret	# far returns??
	ret	$0x2222

	# opcode D0
	salb	$1, %bh
	salb	$1, 0x6234(%ebx, %eax, 2)
	salb	%cl, %cl
	salb	$0x7F, %dh

	salw	$1, %bx
	salw	$1, 0x6234(%ebx, %eax, 2)
	salw	%cl, %cx
	salw	$0x7F, %dx

	sall	$1, %ebx
	sall	$1, 0x6234(%ebx, %eax, 2)
	sall	%cl, %ecx
	sall	$0x7F, %edx
	
	# opcode D0
	sarb	$1, %bh
	sarb	$1, 0x6234(%ebx, %eax, 2)
	sarb	%cl, %cl
	sarb	$0x7F, %dh

	sarw	$1, %bx
	sarw	$1, 0x6234(%ebx, %eax, 2)
	sarw	%cl, %cx
	sarw	$0x7F, %dx

	sarl	$1, %ebx
	sarl	$1, 0x6234(%ebx, %eax, 2)
	sarl	%cl, %ecx
	sarl	$0x7F, %edx

	# opcode FD
	std

	# opcode 90
	xchg	%dx, %ax
	xchg	%edx, %eax
	xchgb	%ch, %es:0x62463444(%edx, %ecx, 4)
	xchgw	%cx, %fs:0x62463444(%esi, %ebx, 4)
	xchgl	%ecx, %gs:0x62463444(%edx, %eax, 4)
