@R0
D = M
@x
M = D

@R1
D = M
@y
M = D

@R2
D = M
@z
M = D

@R3
D = M
@w
M = D

@R4
D = M
@u
M = D


@x
D = M
	
@R5
M = D
	
@y
D = M

@R5
D = M - D

@P1
D; JGE

@y
D = M

@R5
M = D

(P1)

@z
D = M
	
@R5
D = M - D

@P2
D; JGE	

@z
D = M

@R5
M = D

(P2)

@w
D = M
	
@R5
D = M - D

@P3
D; JGE

@w
D = M

@R5
M = D

(P3)

@u
D = M
	
@R5
D = M - D

@P4
D; JGE

@u
D = M

@R5
M = D	
	
(P4)
	
(END)
@END
0;JMP
