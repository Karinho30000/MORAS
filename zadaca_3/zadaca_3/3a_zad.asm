@1
D = M

@e
M = D

@SKIP
D;JGT

@2
M=1

@END
0;JMP

(SKIP)
@0
D = M

@bs
M = D

@2
M = D

@x
M = D

(POTSTART)
@e
D = M

@POTEND
D-1;JEQ

(LOOP_START)
@bs
D = M

@LOOP_END
D-1;JEQ

@x
D = M

@2
M = M + D

@bs
M = M - 1

@LOOP_START
0;JMP

(LOOP_END)

@2
D = M

@x
M = D

@0
D = M

@bs
M = D

@e
M = M-1

@POTSTART
0;JMP

(POTEND)

(END)
@END
0;JMP