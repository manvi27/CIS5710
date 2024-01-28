        .section .data
input_string:   .asciz "Hello world!"

        # tohost/fromhost are data locations used by Spike
        .align 8
tohost: .byte 0
        .align 8
fromhost: .byte 0

        
        .section .text
        .globl _start
_start:
        # Load the address of the input string into a0
        la a0, input_string
        # Your code here!
        li a3,122  #ascii for z
        li a4,97   #ascii for a
_loop:  
        lb a2,0(a0) #a2 = str[i], a0 = &str[i]
        beqz a2,end_program  # if(str[i] == '\0') end_program         
        bgt a2,a3,_incr
        blt a2,a4,_incr 
_mod:
        addi a2,a2,-32
        sb a2,0(a0) 
_incr:
        addi a0,a0,1 #i = i+1
        j _loop 
        
end_program:
        # jump here when you're done
        j end_program


#for(i = 0; input_string[i] != '\0';i++)
#{
#        if(input_string[i]  > 90)
#        {
#                input_string[i] = input_string[i] - 32;
#        }
#}
