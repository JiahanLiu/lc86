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
//module regfile8x32e (IN0, IN1, IN2, 
//		     R0, R1, R2, R3, RE0, RE1, RE2, RE3,
//		     WR0, WR1, WR2, WE0, WE1, WE2, 
//		     OUT0, OUT1, OUT2, OUT3, CLK);
//   input [31:0] IN0, IN1, IN2;
//   input [2:0] 	R0, R1, R2, R3;
//   
//   input [1:0] 	RE0, RE1, RE2, RE3; // read enable type (8lo, 8hi, 16, 32)
//
//   input [2:0] 	WR0, WR1, WR2;
//   input [1:0] 	WE0, WE1, WE2; // write enable type (8lo, 8hi, 16, 32)
//   input 	CLK;
//   
//   output [31:0] OUT0, OUT1, OUT2, OUT3;
//
//endmodule // regfile8x32e

module regfile8x32e (
    input clk,
    input [31:0] result1, result2, result3,
    input [2:0] SR1, SR2, SR3, SR4,
    input [1:0]	RE4, RE1, RE2, RE3;
    input [2:0] DR1, DR2, DR3,
    input write_DR1, write_DR2, write_DR3,
    input [1:0] WE1, WE2, WE3,
    output [31:0] regA, regB, regC, regD
);

wire write_DR1_buf, write_DR2_buf, write_DR3_buf;
wire [7:0] write_hh_en1, write_hh_en2, write_hh_en3;
wire [7:0] write_hl_en1, write_hl_en2, write_hl_en3;
wire [7:0] write_lh_en1, write_lh_en2, write_lh_en3;
wire [7:0] write_ll_en1, write_ll_en2, write_ll_en3;
wire [7:0] write_hh_en1_b, write_hh_en2_b, write_hh_en3_b;
wire [7:0] write_hl_en1_b, write_hl_en2_b, write_hl_en3_b;
wire [7:0] write_lh_en1_b, write_lh_en2_b, write_lh_en3_b;
wire [7:0] write_ll_en1_b, write_ll_en2_b, write_ll_en3_b;
wire [7:0] out1a, out2a, out3a, out4a;
wire [7:0] outw1, outw2, outw3, outw4, outw5, outw6, outw7, outw8;
wire [7:0] outw9, outw10, outw11, outw12;
wire [31:0] write_data0_hh, write_data1_hh, write_data2_hh, write_data3_hh;
wire [31:0] write_data4_hh, write_data5_hh, write_data6_hh, write_data7_hh;
wire [31:0] write_data0_hl, write_data1_hl, write_data2_hl, write_data3_hl;
wire [31:0] write_data4_hl, write_data5_hl, write_data6_hl, write_data7_hl;
wire [31:0] write_data0_lh, write_data1_lh, write_data2_lh, write_data3_lh;
wire [31:0] write_data4_lh, write_data5_lh, write_data6_lh, write_data7_lh;
wire [31:0] write_data0_ll, write_data1_ll, write_data2_ll, write_data3_ll;
wire [31:0] write_data4_ll, write_data5_ll, write_data6_ll, write_data7_ll;
wire [7:0] r_sel1_hh, r_sel0_hh;
wire [7:0] r_sel1_hl, r_sel0_hl;
wire [7:0] r_sel1_lh, r_sel0_lh;
wire [7:0] r_sel1_ll, r_sel0_ll;
wire r_sel00_buf, r_sel01_buf, r_sel02_buf, r_sel03_buf, r_sel04_buf;
wire r_sel05_buf, r_sel06_buf, r_sel07_buf;
wire r_sel10_buf, r_sel11_buf, r_sel12_buf, r_sel13_buf, r_sel14_buf;
wire r_sel15_buf, r_sel16_buf, r_sel17_buf;
wire [31:0] reg0_out, reg1_out, reg2_out, reg3_out;
wire [31:0] reg4_out, reg5_out, reg6_out, reg7_out;
wire [31:0] out1m, out2m, out3m, out4m, out5m, out6m, out7m, out8m;
wire SR10, SR11, SR12;
wire SR20, SR21, SR22;
wire SR30, SR31, SR32;
wire SR40, SR41, SR42;
wire sr1_sel0, sr1_sel1, sr1_sel2, sr1_sel3;
wire sr2_sel0, sr2_sel1, sr2_sel2, sr2_sel3;
wire sr3_sel0, sr3_sel1, sr3_sel2, sr3_sel3;
wire sr4_sel0, sr4_sel1, sr4_sel2, sr4_sel3;
wire RE10_b, RE20_b, RE30_b, RE40_b;
wire outas1, outas2, outas3, outas4;

bufferH16$ buf1 (write_DR1_buf, write_DR1);
bufferH16$ buf2 (write_DR2_buf, write_DR2);
bufferH16$ buf3 (write_DR3_buf, write_DR3);

register_file_decoder u_register_file_decoder1 (DR1, WE1, write_hh_en1, write_hl_en1, write_lh_en1, write_ll_en1);
register_file_decoder u_register_file_decoder2 (DR2, WE2, write_hh_en2, write_hl_en2, write_lh_en2, write_ll_en2);
register_file_decoder u_register_file_decoder3 (DR3, WE3, write_hh_en3, write_hl_en3, write_lh_en3, write_ll_en3);

and2$ andw1[7:0] (outw1, write_hh_en1, write_DR1_buf);
and2$ andw2[7:0] (outw2, write_hl_en1, write_DR1_buf);
and2$ andw3[7:0] (outw3, write_lh_en1, write_DR1_buf);
and2$ andw4[7:0] (outw4, write_ll_en1, write_DR1_buf);

and2$ andw5[7:0] (outw5, write_hh_en2, write_DR2_buf);
and2$ andw6[7:0] (outw6, write_hl_en2, write_DR2_buf);
and2$ andw7[7:0] (outw7, write_lh_en2, write_DR2_buf);
and2$ andw8[7:0] (outw8, write_ll_en2, write_DR2_buf);

and2$ andw9[7:0] (outw9, write_hh_en3, write_DR3_buf);
and2$ andw10[7:0] (outw10, write_hl_en3, write_DR3_buf);
and2$ andw11[7:0] (outw11, write_lh_en3, write_DR3_buf);
and2$ andw12[7:0] (outw12, write_ll_en3, write_DR3_buf);


or3$ or1[7:0] (out1a, outw1, outw5, outw9);
or3$ or2[7:0] (out2a, outw2, outw6, outw10);
or3$ or3[7:0] (out3a, outw3, outw7, outw11);
or3$ or4[7:0] (out4a, outw4, outw8, outw12);

// Here d1, d2, d3 are write_en1, write_en2, write_en3
// s1 = (!d1 &!d2 &d3);
// s0 = (!d1 &d2 &!d3);

inv1$ inv1[7:0] (write_hh_en1_b, write_hh_en1);
inv1$ inv2[7:0] (write_hh_en2_b, write_hh_en2);
inv1$ inv3[7:0] (write_hh_en3_b, write_hh_en3);

inv1$ inv4[7:0] (write_hl_en1_b, write_hl_en1);
inv1$ inv5[7:0] (write_hl_en2_b, write_hl_en2);
inv1$ inv6[7:0] (write_hl_en3_b, write_hl_en3);

inv1$ inv7[7:0] (write_lh_en1_b, write_lh_en1);
inv1$ inv8[7:0] (write_lh_en2_b, write_lh_en2);
inv1$ inv9[7:0] (write_lh_en3_b, write_lh_en3);

inv1$ inv10[7:0] (write_ll_en1_b, write_ll_en1);
inv1$ inv11[7:0] (write_ll_en2_b, write_ll_en2);
inv1$ inv12[7:0] (write_ll_en3_b, write_ll_en3);


// Write the correct data
and3$ and2[7:0] (r_sel1_hh, write_hh_en1_b, write_hh_en2_b, write_hh_en3);
and3$ and3[7:0] (r_sel0_hh, write_hh_en1_b, write_hh_en2, write_hh_en3_b);

and3$ and4[7:0] (r_sel1_hl, write_hl_en1_b, write_hl_en2_b, write_hl_en3);
and3$ and5[7:0] (r_sel0_hl, write_hl_en1_b, write_hl_en2, write_hl_en3_b);

and3$ and6[7:0] (r_sel1_lh, write_lh_en1_b, write_lh_en2_b, write_lh_en3);
and3$ and7[7:0] (r_sel0_lh, write_lh_en1_b, write_lh_en2, write_lh_en3_b);

and3$ and8[7:0] (r_sel1_ll, write_ll_en1_b, write_ll_en2_b, write_ll_en3);
and3$ and9[7:0] (r_sel0_ll, write_ll_en1_b, write_ll_en2, write_ll_en3_b);


mux4_8$ mux0_hh[3:0] (write_data0_hh, result1, result2, result3, , r_sel0_hh[0], r_sel1_hh[0]);
mux4_8$ mux1_hh[3:0] (write_data1_hh, result1, result2, result3, , r_sel0_hh[1], r_sel1_hh[1]);
mux4_8$ mux2_hh[3:0] (write_data2_hh, result1, result2, result3, , r_sel0_hh[2], r_sel1_hh[2]);
mux4_8$ mux3_hh[3:0] (write_data3_hh, result1, result2, result3, , r_sel0_hh[3], r_sel1_hh[3]);
mux4_8$ mux4_hh[3:0] (write_data4_hh, result1, result2, result3, , r_sel0_hh[4], r_sel1_hh[4]);
mux4_8$ mux5_hh[3:0] (write_data5_hh, result1, result2, result3, , r_sel0_hh[5], r_sel1_hh[5]);
mux4_8$ mux6_hh[3:0] (write_data6_hh, result1, result2, result3, , r_sel0_hh[6], r_sel1_hh[6]);
mux4_8$ mux7_hh[3:0] (write_data7_hh, result1, result2, result3, , r_sel0_hh[7], r_sel1_hh[7]);

mux4_8$ mux0_hl[3:0] (write_data0_hl, result1, result2, result3, , r_sel0_hl[0], r_sel1_hl[0]);
mux4_8$ mux1_hl[3:0] (write_data1_hl, result1, result2, result3, , r_sel0_hl[1], r_sel1_hl[1]);
mux4_8$ mux2_hl[3:0] (write_data2_hl, result1, result2, result3, , r_sel0_hl[2], r_sel1_hl[2]);
mux4_8$ mux3_hl[3:0] (write_data3_hl, result1, result2, result3, , r_sel0_hl[3], r_sel1_hl[3]);
mux4_8$ mux4_hl[3:0] (write_data4_hl, result1, result2, result3, , r_sel0_hl[4], r_sel1_hl[4]);
mux4_8$ mux5_hl[3:0] (write_data5_hl, result1, result2, result3, , r_sel0_hl[5], r_sel1_hl[5]);
mux4_8$ mux6_hl[3:0] (write_data6_hl, result1, result2, result3, , r_sel0_hl[6], r_sel1_hl[6]);
mux4_8$ mux7_hl[3:0] (write_data7_hl, result1, result2, result3, , r_sel0_hl[7], r_sel1_hl[7]);

mux4_8$ mux0_lh[3:0] (write_data0_lh, result1, result2, result3, , r_sel0_lh[0], r_sel1_lh[0]);
mux4_8$ mux1_lh[3:0] (write_data1_lh, result1, result2, result3, , r_sel0_lh[1], r_sel1_lh[1]);
mux4_8$ mux2_lh[3:0] (write_data2_lh, result1, result2, result3, , r_sel0_lh[2], r_sel1_lh[2]);
mux4_8$ mux3_lh[3:0] (write_data3_lh, result1, result2, result3, , r_sel0_lh[3], r_sel1_lh[3]);
mux4_8$ mux4_lh[3:0] (write_data4_lh, result1, result2, result3, , r_sel0_lh[4], r_sel1_lh[4]);
mux4_8$ mux5_lh[3:0] (write_data5_lh, result1, result2, result3, , r_sel0_lh[5], r_sel1_lh[5]);
mux4_8$ mux6_lh[3:0] (write_data6_lh, result1, result2, result3, , r_sel0_lh[6], r_sel1_lh[6]);
mux4_8$ mux7_lh[3:0] (write_data7_lh, result1, result2, result3, , r_sel0_lh[7], r_sel1_lh[7]);

mux4_8$ mux0_ll[3:0] (write_data0_ll, result1, result2, result3, , r_sel0_ll[0], r_sel1_ll[0]);
mux4_8$ mux1_ll[3:0] (write_data1_ll, result1, result2, result3, , r_sel0_ll[1], r_sel1_ll[1]);
mux4_8$ mux2_ll[3:0] (write_data2_ll, result1, result2, result3, , r_sel0_ll[2], r_sel1_ll[2]);
mux4_8$ mux3_ll[3:0] (write_data3_ll, result1, result2, result3, , r_sel0_ll[3], r_sel1_ll[3]);
mux4_8$ mux4_ll[3:0] (write_data4_ll, result1, result2, result3, , r_sel0_ll[4], r_sel1_ll[4]);
mux4_8$ mux5_ll[3:0] (write_data5_ll, result1, result2, result3, , r_sel0_ll[5], r_sel1_ll[5]);
mux4_8$ mux6_ll[3:0] (write_data6_ll, result1, result2, result3, , r_sel0_ll[6], r_sel1_ll[6]);
mux4_8$ mux7_ll[3:0] (write_data7_ll, result1, result2, result3, , r_sel0_ll[7], r_sel1_ll[7]);


// Registers[31:24] 
reg32e$ reg0_hh (.CLK(clk), .Din(write_data0_hh), .Q(reg0_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out1a[0]) );
reg32e$ reg1_hh (.CLK(clk), .Din(write_data1_hh), .Q(reg1_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out1a[1]) );
reg32e$ reg2_hh (.CLK(clk), .Din(write_data2_hh), .Q(reg2_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out1a[2]) );
reg32e$ reg3_hh (.CLK(clk), .Din(write_data3_hh), .Q(reg3_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out1a[3]) );
reg32e$ reg4_hh (.CLK(clk), .Din(write_data4_hh), .Q(reg4_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out1a[4]) );
reg32e$ reg5_hh (.CLK(clk), .Din(write_data5_hh), .Q(reg5_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out1a[5]) );
reg32e$ reg6_hh (.CLK(clk), .Din(write_data6_hh), .Q(reg6_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out1a[6]) );
reg32e$ reg7_hh (.CLK(clk), .Din(write_data7_hh), .Q(reg7_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out1a[7]) );

// Registers[23:16] 
reg32e$ reg0_hl (.CLK(clk), .Din(write_data0_hl), .Q(reg0_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out2a[0]) );
reg32e$ reg1_hl (.CLK(clk), .Din(write_data1_hl), .Q(reg1_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out2a[1]) );
reg32e$ reg2_hl (.CLK(clk), .Din(write_data2_hl), .Q(reg2_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out2a[2]) );
reg32e$ reg3_hl (.CLK(clk), .Din(write_data3_hl), .Q(reg3_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out2a[3]) );
reg32e$ reg4_hl (.CLK(clk), .Din(write_data4_hl), .Q(reg4_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out2a[4]) );
reg32e$ reg5_hl (.CLK(clk), .Din(write_data5_hl), .Q(reg5_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out2a[5]) );
reg32e$ reg6_hl (.CLK(clk), .Din(write_data6_hl), .Q(reg6_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out2a[6]) );
reg32e$ reg7_hl (.CLK(clk), .Din(write_data7_hl), .Q(reg7_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out2a[7]) );

// Registers[15:8] 
reg32e$ reg0_lh (.CLK(clk), .Din(write_data0_lh), .Q(reg0_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out3a[0]) );
reg32e$ reg1_lh (.CLK(clk), .Din(write_data1_lh), .Q(reg1_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out3a[1]) );
reg32e$ reg2_lh (.CLK(clk), .Din(write_data2_lh), .Q(reg2_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out3a[2]) );
reg32e$ reg3_lh (.CLK(clk), .Din(write_data3_lh), .Q(reg3_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out3a[3]) );
reg32e$ reg4_lh (.CLK(clk), .Din(write_data4_lh), .Q(reg4_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out3a[4]) );
reg32e$ reg5_lh (.CLK(clk), .Din(write_data5_lh), .Q(reg5_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out3a[5]) );
reg32e$ reg6_lh (.CLK(clk), .Din(write_data6_lh), .Q(reg6_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out3a[6]) );
reg32e$ reg7_lh (.CLK(clk), .Din(write_data7_lh), .Q(reg7_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out3a[7]) );

// Registers[7:0] 
reg32e$ reg0_ll (.CLK(clk), .Din(write_data0_ll), .Q(reg0_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out4a[0]) );
reg32e$ reg1_ll (.CLK(clk), .Din(write_data1_ll), .Q(reg1_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out4a[1]) );
reg32e$ reg2_ll (.CLK(clk), .Din(write_data2_ll), .Q(reg2_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out4a[2]) );
reg32e$ reg3_ll (.CLK(clk), .Din(write_data3_ll), .Q(reg3_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out4a[3]) );
reg32e$ reg4_ll (.CLK(clk), .Din(write_data4_ll), .Q(reg4_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out4a[4]) );
reg32e$ reg5_ll (.CLK(clk), .Din(write_data5_ll), .Q(reg5_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out4a[5]) );
reg32e$ reg6_ll (.CLK(clk), .Din(write_data6_ll), .Q(reg6_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out4a[6]) );
reg32e$ reg7_ll (.CLK(clk), .Din(write_data7_ll), .Q(reg7_out), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(out4a[7]) );


bufferH16$ bufs1 (SR10, SR1[0]);
bufferH16$ bufs2 (SR11, SR1[1]);
bufferH16$ bufs3 (SR12, SR1[2]);

bufferH16$ bufs4 (SR20, SR2[0]);
bufferH16$ bufs5 (SR21, SR2[1]);
bufferH16$ bufs6 (SR22, SR2[2]);

bufferH16$ bufs7 (SR30, SR3[0]);
bufferH16$ bufs8 (SR31, SR3[1]);
bufferH16$ bufs9 (SR32, SR3[2]);

bufferH16$ bufs10 (SR40, SR4[0]);
bufferH16$ bufs11 (SR41, SR4[1]);
bufferH16$ bufs12 (SR42, SR4[2]);

// Generate seelct signals for masking
inv1$ invs1 (RE10_b, RE1[0]);
inv1$ invs2 (RE20_b, RE2[0]);
inv1$ invs3 (RE30_b, RE3[0]);
inv1$ invs4 (RE40_b, RE4[0]);

or2$ ors1 (sr1_sel0, RE1[1], RE10_b);
assign sr1_sel1 = RE1[1];
and2$ ands1 (outas1, RE1[0], RE1[1]);
assign sr1_sel2 = outas1;
assign sr1_sel3 = outas1;

or2$ ors2 (sr2_sel0, RE2[1], RE20_b);
assign sr2_sel1 = RE2[1];
and2$ ands2 (outas2, RE2[0], RE2[1]);
assign sr2_sel2 = outas2;
assign sr2_sel3 = outas2;

or2$ ors3 (sr3_sel0, RE3[1], RE30_b);
assign sr3_sel1 = RE3[1];
and2$ ands3 (outas3, RE3[0], RE3[1]);
assign sr3_sel2 = outas3;
assign sr3_sel3 = outas3;

or2$ ors4 (sr4_sel0, RE4[1], RE40_b);
assign sr4_sel1 = RE4[1];
and2$ ands4 (outas4, RE4[0], RE4[1]);
assign sr4_sel2 = outas4;
assign sr4_sel3 = outas4;

assign reg0_out = {reg0_hh[31:24], reg0_hl[23:16], reg0_lh[15:8], reg0_ll[7:0]};
assign reg1_out = {reg1_hh[31:24], reg1_hl[23:16], reg1_lh[15:8], reg1_ll[7:0]};
assign reg2_out = {reg2_hh[31:24], reg2_hl[23:16], reg2_lh[15:8], reg2_ll[7:0]};
assign reg3_out = {reg3_hh[31:24], reg3_hl[23:16], reg3_lh[15:8], reg3_ll[7:0]};
assign reg4_out = {reg4_hh[31:24], reg4_hl[23:16], reg4_lh[15:8], reg4_ll[7:0]};
assign reg5_out = {reg5_hh[31:24], reg5_hl[23:16], reg5_lh[15:8], reg5_ll[7:0]};
assign reg6_out = {reg6_hh[31:24], reg6_hl[23:16], reg6_lh[15:8], reg6_ll[7:0]};
assign reg7_out = {reg7_hh[31:24], reg7_hl[23:16], reg7_lh[15:8], reg7_ll[7:0]};

// Read SR1
mux4_8$ amux0[3:0] (out1m, reg0_out, reg1_out, reg2_out, reg3_out, SR10, SR11);
mux4_8$ amux1[3:0] (out2m, reg4_out, reg5_out, reg6_out, reg7_out, SR10, SR11);
mux2_8$ amux2[3:0] (regA_out, out1m, out2m, SR12);

// Mask the read value according to the size
mux2_8$ amuxm0 (regA[7:0], regA_out[15:8], regA_out[7:0], sr1_sel0);
mux2_8$ amuxm1 (regA[15:8], 8'b0, regA_out[15:8], sr1_sel1);
mux2_8$ amuxm2 (regA[23:16], 8'b0, regA_out[23:16], sr1_sel2);
mux2_8$ amuxm3 (regA[31:23], 8'b0, regA_out[31:24], sr1_sel3);

//Read SR2
mux4_8$ bmux0[3:0] (out3m, reg0_out, reg1_out, reg2_out, reg3_out, SR20, SR21);
mux4_8$ bmux1[3:0] (out4m, reg4_out, reg5_out, reg6_out, reg7_out, SR20, SR21);
mux2_8$ bmux2[3:0] (regB_out, out3m, out4m, SR22);

mux2_8$ bmuxm0 (regB[7:0], regB_out[15:8], regB_out[7:0], sr2_sel0);
mux2_8$ bmuxm1 (regB[15:8], 8'b0, regB_out[15:8], sr2_sel1);
mux2_8$ bmuxm2 (regB[23:16], 8'b0, regB_out[23:16], sr2_sel2);
mux2_8$ bmuxm3 (regB[31:23], 8'b0, regB_out[31:24], sr2_sel3);

// Read SR3
mux4_8$ cmux0[3:0] (out5m, reg0_out, reg1_out, reg2_out, reg3_out, SR30, SR31);
mux4_8$ cmux1[3:0] (out6m, reg4_out, reg5_out, reg6_out, reg7_out, SR30, SR31);
mux2_8$ cmux2[3:0] (regC_out, out5m, out6m, SR32);

mux2_8$ cmuxm0 (regC[7:0], regC_out[15:8], regC_out[7:0], sr3_sel0);
mux2_8$ cmuxm1 (regC[15:8], 8'b0, regC_out[15:8], sr3_sel1);
mux2_8$ cmuxm2 (regC[23:16], 8'b0, regC_out[23:16], sr3_sel2);
mux2_8$ cmuxm3 (regC[31:23], 8'b0, regC_out[31:24], sr3_sel3);

// Read SR4
mux4_8$ dmux0[3:0] (out7m, reg0_out, reg1_out, reg2_out, reg3_out, SR40, SR41);
mux4_8$ dmux1[3:0] (out8m, reg4_out, reg5_out, reg6_out, reg7_out, SR40, SR41);
mux2_8$ dmux2[3:0] (regD_out, out7m, out8m, SR42);

mux2_8$ cmuxm0 (regD[7:0], regD_out[15:8], regD_out[7:0], sr4_sel0);
mux2_8$ cmuxm1 (regD[15:8], 8'b0, regD_out[15:8], sr4_sel1);
mux2_8$ cmuxm2 (regD[23:16], 8'b0, regD_out[23:16], sr4_sel2);
mux2_8$ cmuxm3 (regD[31:23], 8'b0, regD_out[31:24], sr4_sel3);

endmodule
