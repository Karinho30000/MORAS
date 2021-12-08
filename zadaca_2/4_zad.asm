@i
M = 0

(LOOP_START)
	@4096
	D = A

	@i
	D = M - D

	@LOOP_END
	D; JGT

	@18498
	D = A

	@x
	D = D + M
	
	@i
	A = M + D
	M = 1
	
	@32
	D = A
	
	@i
	M = D + M
	
	@LOOP_START
	0; JMP
	
(LOOP_END)

//samo paralelna stranica

(END)
@END
0;JMP
	
	