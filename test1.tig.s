.text
.globl tigermain
.type tigermain, @function
tigermain:
subq $0, %rsp
.L5:
movq $1, %rax
movq $2, %rdi
movq $0, %r11
cmpq %r11, %rax
jne .L1
.L2:
movq $3, %rdi
.L3:
call printi
jmp .L4
.L1:
movq %rax, %rdi
jmp .L3
.L4:
addq $0, %rsp
ret

