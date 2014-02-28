
		 .text
		 .globl _entry
_entry:
		 pushl %ebp
		 movl %esp,%ebp
		 pushl $0
		 popl %eax
		 movl %eax,i
		 pushl %eax
		 popl %eax
		 pushl $0
		 popl %eax
		 movl %eax,j
		 pushl %eax
		 popl %eax
		 pushl $0
		 popl %eax
		 movl %eax,a
		 pushl %eax
		 popl %eax
		  call init_threads
		 movl $L9,%eax
		 call set_second_thread
L8:
		 jmp L2
L3:
		 pushl a
		 pushl $1
		 popl %ebx
		 call cosw  # randomly inserted context switch
		 popl %eax
		 addl %ebx,%eax
		 call cosw  # randomly inserted context switch
		 pushl %eax
		 popl %eax
		 movl %eax,a
		 pushl %eax
		 popl %eax
		 pushl i
		 pushl $1
		 popl %ebx
		 popl %eax
		 addl %ebx,%eax
		 pushl %eax
		 popl %eax
		 movl %eax,i
		 pushl %eax
		 popl %eax
L2:
		 pushl i
		 pushl $10
		 popl %eax
		 popl %ebx
		 cmpl %eax,%ebx
		 jge L0
		 pushl $1
		 jmp L1
L0:
		 pushl $0
L1:
		 popl %eax
		 cmpl $0,%eax
		 jne L3
		 call cosw  # randomly inserted context switch
		 jmp L10
L9:
		 jmp L6
		 call cosw  # randomly inserted context switch
L7:
		 pushl a
		 pushl $1
		 popl %ebx
		 popl %eax
		 subl %ebx,%eax
		 pushl %eax
		 popl %eax
		 movl %eax,a
		 pushl %eax
		 popl %eax
		 pushl j
		 pushl $1
		 popl %ebx
		 popl %eax
		 addl %ebx,%eax
		 pushl %eax
		 popl %eax
		 movl %eax,j
		 pushl %eax
		 popl %eax
L6:
		 pushl j
		 pushl $10
		 popl %eax
		 popl %ebx
		 cmpl %eax,%ebx
		 jge L4
		 pushl $1
		 call cosw  # randomly inserted context switch
		 jmp L5
L4:
		 pushl $0
L5:
		 popl %eax
		 cmpl $0,%eax
		 jne L7
 L10:
		 call single_thread
		 movl %ebp,%esp
		 popl %ebp
		 ret

		 .data
		 .globl __var_area
__var_area:

i:		 .long 0
a:		 .long 0
j:		 .long 0

		 .globl __var_name_area
__var_name_area:

i_name:	 .asciz "i"
a_name:	 .asciz "a"
j_name:	 .asciz "j"

		 .globl __var_ptr_area
__var_ptr_area:

i_ptr:	 .long i_name
a_ptr:	 .long a_name
j_ptr:	 .long j_name

__end_var_ptr_area:	 .long 0
