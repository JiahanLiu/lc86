module register_file (CLK, 
		      SEG_DIN, SEGID1, SEGID2, WRSEGID, SEGWE,
		      MM_DIN, MMID1, MMID2, WRMMID, MMWE, 
		      GPR_DIN0, GPR_DIN1, GPR_DIN2, 
		      GPRID0, GPRID1, GPRID2, GPRID3,
		      GPR_RE0, GPR_RE1, GPR_RE2, GPR_RE3,
		      WRGPR0, WRGPR1, WRGPR2, GPRWE0, GPRWE1, GPRWE2,
		      CS_DIN, EIP_DIN, EFLAGS_DIN,
		      LD_CS, LD_EIP, LD_EFLAGS,
		      SEGDOUT1, SEGDOUT2, MMDOUT1, MMDOUT2,
		      GPRDOUT0, GPRDOUT1, GPRDOUT2, GPRDOUT3,
		      CSDOUT, EIPDOUT, EFLAGSDOUT);

   input CLK;
   
   input [15:0] SEG_DIN;
   input [2:0] 	SEGID1, SEGID2, WRSEGID;
   input 	SEGWE;

   input [63:0] MM_DIN;
   input [2:0] 	MMID1, MMID2, WRMMID;
   input 	MMWE;

   input [31:0] GPR_DIN0, GPR_DIN1, GPR_DIN2;
   input [2:0] 	GPRID0, GPRID1, GPRID2, GPRID3,
		WRGPR0, WRGPR1, WRGPR2;
   input [1:0] 	GPR_RE0, GPR_RE1, GPR_RE2, GPR_RE3,
		GPRWE0, GPRWE1, GPRWE2;

   input [16:0] CS_DIN;
   input [31:0] EIP_DIN, EFLAGS_DIN;

   input 	LD_CS, LD_EIP, LD_EFLAGS;
	 
   output [15:0] SEGDOUT1, SEGDOUT2;
   output [63:0] MMDOUT1, MMDOUT2;
   output [31:0] GPRDOUT0, GPRDOUT1, GPRDOUT2, GPRDOUT3;

   output [15:0] CSDOUT;
   output [31:0] EIPDOUT;
   output [31:0] EFLAGSDOUT;
	       
   wire [15:0] cs_unused;
   
   regfile8x16  segr (SEG_DIN, SEGID1, SEGID2, 1'b1, 1'b1, WRSEGID, SEGWE, SEGDOUT1, SEGDOUT2, CLK);
   regfile8x64  mmr  (MM_DIN, MMID1, MMID2, 1'b1, 1'b1, WRMMID, MMWE, MMDOUT1, MMDOUT2, CLK);
   regfile8x32e gpr  (GPR_DIN0, GPR_DIN1, GPR_DIN2, 
		      GPRID0, GPRID1, GPRID2, GPRID3, GPR_RE0, GPR_RE1, GPR_RE2, GPR_RE3, 
		      WRGPR0, WRGPR1, WRGPR2, GPRWE0, GPRWE1, GPRWE2, 
		      GPRDOUT0, GPRDOUT1, GPRDOUT2, GPRDOUT3, CLK);

   // Format: reg32e$(CLK, Din, Q, QBAR, CLR, PRE,en);
   reg32e$
     segr_cs (CLK, {16'b0, CS_DIN}, {cs_unused, CSDOUT}, , 1'b1, 1'b1, LD_CS),
     eip     (CLK, EIP_DIN, EIPDOUT, , 1'b1, 1'b1, LD_EIP),
     eflags  (CLK, EFLAGS_DIN, EFLAGSDOUT, , 1'b1', 1'b1, LD_EFLAGS);
     
endmodule // register_file

// Segment Registers
module regfile8x16 (IN0, R1, R2, RE1, RE2, W, WE, OUT1, OUT2, CLOCK);
   input [15:0] IN0;
   input [2:0] R1;
   input [2:0] R2;
   
   input       RE1;
   input       RE2;

   input [2:0] W;
   input       WE;
   input       CLOCK;
   
   output [15:0] OUT1;
   output [15:0] OUT2;

   regfile8x8$ 
     regfilelo (IN0[7:0], R1, R2, RE1, RE2, W, WE, OUT1[7:0], OUT2[7:0], CLOCK),
     regfilehi (IN0[15:8], R1, R2, RE1, RE2, W, WE, OUT1[15:8], OUT2[15:8], CLOCK);

endmodule // regfile8x16

module regfile8x32 (IN0, R1, R2, RE1, RE2, W, WE, OUT1, OUT2, CLOCK);
   input [31:0] IN0;
   input [2:0] R1;
   input [2:0] R2;
   
   input       RE1;
   input       RE2;

   input [2:0] W;
   input       WE;
   input       CLOCK;
   
   output [31:0] OUT1;
   output [31:0] OUT2;

   regfile8x16$ 
     regfilelo (IN0[15:0], R1, R2, RE1, RE2, W, WE, OUT1[15:0], OUT2[15:0], CLOCK),
     regfilehi (IN0[31:16], R1, R2, RE1, RE2, W, WE, OUT1[31:16], OUT2[31:16], CLOCK);
endmodule // regfile8x32

module regfile8x64 (IN0, R1, R2, RE1, RE2, W, WE, OUT1, OUT2, CLOCK);
   input [63:0] IN0;
   input [2:0] R1;
   input [2:0] R2;
   
   input       RE1;
   input       RE2;

   input [2:0] W;
   input       WE;
   input       CLOCK;
   
   output [63:0] OUT1;
   output [63:0] OUT2;

   regfile8x32$ 
     regfilelo (IN0[31:0], R1, R2, RE1, RE2, W, WE, OUT1[31:0], OUT2[31:0], CLOCK),
     regfilehi (IN0[63:32], R1, R2, RE1, RE2, W, WE, OUT1[63:32], OUT2[63:32], CLOCK);
endmodule // regfile8x64

/* 
 For GPRs, Want 4 read ports and 3 write ports
 4 read for CMPXCHG (implicit AL/AX/EAX
 3 write for REP (ECX, DS:ESI, ES:EDI
 */
module regfile8x32e (IN0, IN1, IN2, 
		     R0, R1, R2, R3, RE0, RE1, RE2, RE3,
		     WR0, WR1, WR2, WE0, WE1, WE2, 
		     OUT0, OUT1, OUT2, OUT3, CLK);
   input [31:0] IN0, IN1, IN2;
   input [2:0] 	R0, R1, R2, R3;
   
   input [1:0] 	RE0, RE1, RE2, RE3; // read enable type (8lo, 8hi, 16, 32)

   input [2:0] 	WR0, WR1, WR2;
   input [1:0] 	WE0, WE1, WE2; // write enable type (8lo, 8hi, 16, 32)
   input 	CLK;
   
   output [31:0] OUT0, OUT1, OUT2, OUT3;

endmodule // regfile8x32e
