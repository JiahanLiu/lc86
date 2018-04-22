// 16 bytes from icache in one access
module fetch (
    input clk, set, reset,
    input [31:0] EIP,
    input [127:0] icache_data,
    input icache_ready,
    input [31:0] jmp_fp, trap_fp,
    input [15:0] CS,
    input [1:0] fp_mux,
    input load_eip,

    output [31:0] EIP_OUT,
    output [15:0] CS_OUT,
    output icache_en,
    output [31:0] icache_address,
    output segment_limit_exception,
    output [127:0] IR_OUT,

    output [3:0] instr_length_updt,
    output [15:0] opcode,
    output [1:0] prefix_size,
    output prefix_present, segment_override, operand_override, repeat_prefix,
    output modrm_present, imm_present,
    output [1:0] imm_size,
    output sib_present, disp_present, disp_size,
    output [3:0] imm_sel,
    output [2:0] disp_sel,
    output offset_present,
    output opcode_size,
    output [1:0] offset_size,
    output [2:0] segID,
    output [7:0] modrm, sib,
    output [2:0] modrm_sel
);

   //The four buffers for the fetch unit
   wire [127:0]  FE_buf_0_in, FE_buf_1_in, FE_buf_2_in, FE_buf_3_in;	//the buffer register inputs
   wire [127:0]  FE_buf_0_out, FE_buf_1_out, FE_buf_2_out, FE_buf_3_out;
   wire 	 FE_buf_0_en, FE_buf_1_en, FE_buf_2_en, FE_buf_3_en;
   wire [127:0] IR;

   assign FE_buf_0_en = 1;
   assign FE_buf_1_en = 1;
   assign FE_buf_2_en = 1;
   assign FE_buf_3_en = 1;
   assign FE_buf_3_in = 128'h0F6FEB254B212F9681773D090CDB1283;
   assign FE_buf_2_in = 128'h7E6D39201F21D32285BC148878235B49;
   assign FE_buf_1_in = 128'h0F6FEB254B212F9681773D090CDB1283;
   assign FE_buf_0_in = 128'h7E6D39201F21D32285BC148878235B49;
   reg128e$ u_FE_buf_0(clk, FE_buf_0_in, FE_buf_0_out, , reset, set, FE_buf_0_en);
   reg128e$ u_FE_buf_1(clk, FE_buf_1_in, FE_buf_1_out, , reset, set, FE_buf_1_en);
   reg128e$ u_FE_buf_2(clk, FE_buf_2_in, FE_buf_2_out, , reset, set,FE_buf_2_en);
   reg128e$ u_FE_buf_3(clk, FE_buf_3_in, FE_buf_3_out, , reset, set, FE_buf_3_en);

   wire [5:0] read_ptr;

   assign IR_OUT = IR;
   wire [31:0] read_ptr_out;
   wire [31:0] read_ptr_in;
   //temporary read_ptr assign until the fetch is finished
   //Values of the fetch buffers until the fetch unit is finished
   FE_full_shifter FE_full_shifter1 (FE_buf_0_out, FE_buf_1_out, FE_buf_2_out, FE_buf_3_out, read_ptr, IR);

   adder32_w_carry_in add_read_ptr (read_ptr_in, ,{26'h0, read_ptr}, {28'b0, instr_length_updt}, 1'b0);
   reg32e$ IR_2(clk, read_ptr_in, read_ptr_out, ,set, reset, 1'b1);
   assign read_ptr = read_ptr_out[5:0];


   decode_stage1 u_decode_stage1 (clk, set, reset,
				  IR, ,
				  instr_length_updt,
				  opcode,
				  prefix_size,
				  prefix_present, segment_override, operand_override, repeat_prefix,
				  modrm_present, imm_present,
				  imm_size,
				  sib_present, disp_present, disp_size,
				  imm_sel,
				  disp_sel,
				  offset_present,
				  opcode_size,
				  offset_size,
				  segID,
				  modrm, sib,
				  modrm_sel);
   
endmodule

module FE_full_shifter(
    input [127:0] A, B, C, D,
	input [5:0] address,
	output [127:0] OutputA
);

assign dir = 0;
wire [127:0] AB_out, BC_out, CD_out, DA_out;

shift128$ AB(A, B, dir, address[3:0], AB_out);
shift128$ BC(B, C, dir, address[3:0], BC_out);
shift128$ CD(C, D, dir, address[3:0], CD_out);
shift128$ DA(D, A, dir, address[3:0], DA_out);

mux4_128$ selector(OutputA, AB_out, BC_out, CD_out, DA_out, address[4], address[5]);
	
endmodule


module shift128$(
    input [127:0] Din_low,
    input [127:0] Din_high,
    input dir,
    input [3:0] amnt,
    output [127:0] Dout
);


wire [127:0] array [15:0];
wire [127:0] mux_array [3:0];

//genvar i;
//generate
//for(i=0;i<16;i=i+1)
//  begin : generate_loop
//  //Allowed since i is constant when the loop is unrolled
//  assign array[i] = {Din_high[127-i*8:0], Din_low[127:127-i*8]};
//  end
//    endgenerate

assign array[0] = {Din_high[127:0]};
assign array[1] = {Din_high[119:0], Din_low[127:120]};
assign array[2] = {Din_high[111:0], Din_low[127:112]};
assign array[3] = {Din_high[103:0], Din_low[127:104]};
assign array[4] = {Din_high[95:0], Din_low[127:96]};
assign array[5] = {Din_high[87:0], Din_low[127:88]};
assign array[6] = {Din_high[79:0], Din_low[127:80]};
assign array[7] = {Din_high[71:0], Din_low[127:72]};
assign array[8] = {Din_high[63:0], Din_low[127:64]};
assign array[9] = {Din_high[55:0], Din_low[127:56]};
assign array[10] = {Din_high[47:0], Din_low[127:48]};
assign array[11] = {Din_high[39:0], Din_low[127:40]};
assign array[12] = {Din_high[31:0], Din_low[127:32]};
assign array[13] = {Din_high[23:0], Din_low[127:24]};
assign array[14] = {Din_high[15:0], Din_low[127:16]};
assign array[15] = {Din_high[7:0], Din_low[127:8]};

//muxes to select shifted value, first round of muxes
mux4_128$ mux1 (mux_array[0],array[0],array[1],array[2],array[3],amnt[0],amnt[1]);
mux4_128$ mux2 (mux_array[1],array[4],array[5],array[6],array[7],amnt[0],amnt[1]);
mux4_128$ mux3 (mux_array[2],array[8],array[9],array[10],array[11],amnt[0],amnt[1]);
mux4_128$ mux4 (mux_array[3],array[12],array[13],array[14],array[15],amnt[0],amnt[1]);

//last round of muxes
mux4_128$ mux5 (Dout,mux_array[0],mux_array[1],mux_array[2],mux_array[3],amnt[2],amnt[3]);
	

endmodule

module mux4_128$(
    output [127:0] Y,
	input [127:0] IN0,
    input [127:0] IN1, 
    input [127:0] IN2,
    input [127:0] IN3,
	input S0, 
    input S1
);
//genvar i;
//generate
//for(i=0;i<16;i=i+1)
//  begin : generate_loop
//	mux4_8$ mux6 (Y[i*8 +7:i*8], IN0[i*8 +7:i*8], IN1[i*8 +7:i*8], IN2[i*8 +7:i*8], IN3[i*8 +7:i*8],
//			S0, S1);
//  end
//  endgenerate
mux4_8$ mux1 (Y[127:120], IN0[127:120], IN1[127:120], IN2[127:120], IN3[127:120], S0, S1);
mux4_8$ mux2 (Y[119:112], IN0[119:112], IN1[119:112], IN2[119:112], IN3[119:112], S0, S1);
mux4_8$ mux3 (Y[111:104], IN0[111:104], IN1[111:104], IN2[111:104], IN3[111:104], S0, S1);
mux4_8$ mux4 (Y[103:96], IN0[103:96], IN1[103:96], IN2[103:96], IN3[103:96], S0, S1);
mux4_8$ mux5 (Y[95:88], IN0[95:88], IN1[95:88], IN2[95:88], IN3[95:88], S0, S1);
mux4_8$ mux6 (Y[87:80], IN0[87:80], IN1[87:80], IN2[87:80], IN3[87:80], S0, S1);
mux4_8$ mux7 (Y[79:72], IN0[79:72], IN1[79:72], IN2[79:72], IN3[79:72], S0, S1);
mux4_8$ mux8 (Y[71:64], IN0[71:64], IN1[71:64], IN2[71:64], IN3[71:64], S0, S1);
mux4_8$ mux9 (Y[63:56], IN0[63:56], IN1[63:56], IN2[63:56], IN3[63:56], S0, S1);
mux4_8$ mux10 (Y[55:48], IN0[55:48], IN1[55:48], IN2[55:48], IN3[55:48], S0, S1);
mux4_8$ mux11 (Y[47:40], IN0[47:40], IN1[47:40], IN2[47:40], IN3[47:40], S0, S1);
mux4_8$ mux12 (Y[39:32], IN0[39:32], IN1[39:32], IN2[39:32], IN3[39:32], S0, S1);
mux4_8$ mux13 (Y[31:24], IN0[31:24], IN1[31:24], IN2[31:24], IN3[31:24], S0, S1);
mux4_8$ mux14 (Y[23:16], IN0[23:16], IN1[23:16], IN2[23:16], IN3[23:16], S0, S1);
mux4_8$ mux15 (Y[15:8], IN0[15:8], IN1[15:8], IN2[15:8], IN3[15:8], S0, S1);
mux4_8$ mux16 (Y[7:0], IN0[7:0], IN1[7:0], IN2[7:0], IN3[7:0], S0, S1);

endmodule


module reg128e$(
    input CLK,
    input [127:0] Din,
    output [127:0] Q,
    output [127:0] QBAR,
    input CLR,
    input PRE,
    input en
);

reg64e$ low(CLK, Din[63:0], Q[63:0], QBAR[63:0], CLR, PRE, en);
reg64e$ high(CLK, Din[127:64], Q[127:64], QBAR[127:64], CLR, PRE, en);

endmodule


