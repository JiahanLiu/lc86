// 16 bytes from icache in one access

module fetch (
    input clk, set, reset,
    input [31:0] EIP,
    input [127:0] icache_data,
    input icache_ready,
    input [31:0] jmp_fp, trap_fp,
    input [15:0] CS,
    input [3:0] instr_length_updt,
    input [1:0] fp_mux,
    input load_eip,

    output [31:0] EIP_OUT,
    output [15:0] CS_OUT,
    output icache_en,
    output [31:0] icache_address,
    output segment_limit_exception,
    output [127:0] IR
);

//The four buffers for the fetch unit
wire [127:0] FE_buf_0_in, FE_buf_1_in, FE_buf_2_in, FE_buf_3_in;	//the buffer register inputs
wire [127:0] FE_buf_0_out, FE_buf_1_out, FE_buf_2_out, FE_buf_3_out;
wire FE_buf_0_en, FE_buf_1_en, FE_buf_2_en, FE_buf_3_en;
reg128e$ u_FE_buf_0(clk, FE_buf_0_in, FE_buf_0_out, , reset, set, FE_buf_0_en);
reg128e$ u_FE_buf_1(clk, FE_buf_1_in, FE_buf_1_out, , reset, set, FE_buf_1_en);
reg128e$ u_FE_buf_2(clk, FE_buf_2_in, FE_buf_2_out, , reset, set,FE_buf_2_en);
reg128e$ u_FE_buf_3(clk, FE_buf_3_in, FE_buf_3_out, , reset, set, FE_buf_3_en);


wire [5:0] read_ptr;
//temporary read_ptr assign until the fetch is finished
assign read_ptr = 0;
//Values of the fetch buffers until the fetch unit is finished
assign FE_buf_0_in = 128'hFEEDBEEF;
assign FE_buf_1_in = 128'hABCD1234;
assign FE_buf_2_in = 128'hABCD1234;
assign FE_buf_3_in = 128'hABCD1234;
FE_full_shifter(FE_buf_0_out, FE_buf_1_out, FE_buf_2_out, FE_buf_3_out, read_ptr, IR);

endmodule

module FE_full_shifter(input [127:0] A, B, C, D,
			input [5:0] address,
			output [127:0] Output);
wire [127:0] AB_out, BC_out, CD_out, DA_out;
shift126$ AB(A, B, , address[3:0], AB_out);
shift126$ BC(B, C, , address[3:0], BC_out);
shift126$ CD(C, D, , address[3:0], CD_out);
shift128$ DA(D, A, , address[3:0], DA_out);

mux4_128$ selector(Output, AB_out, BC_out, CD_out, DA_out, address[4], address[5]);
	
endmodule

module shift128$(input [127:0] Din_low,
		input [127:0] Din_high,
		input dir,
		input [3:0] amnt,
		output [127:0] Dout);
	wire [3:0] array [127:0];
	wire [1:0] mux_array [127:0];
	genvar i;
for(i=0;i<8;i=i+1)
  begin : generate_loop
  //Allowed since i is constant when the loop is unrolled
  assign array[i] = {Din_high[127-i*8:0], Din_low[127:127-i*8]};
  end

//muxes to select shifted value, first round of muxes
mux4_128$(mux_array[0],array[0],array[1],array[2],array[3],amnt[0],amnt[1]);
mux4_128$(mux_array[1],array[4],array[5],array[6],array[7],amnt[0],amnt[1]);
mux4_128$(mux_array[2],array[8],array[9],array[10],array[11],amnt[0],amnt[1]);
mux4_128$(mux_array[3],array[12],array[13],array[14],array[15],amnt[0],amnt[1]);

//last round of muxes
mux4_128$(Dout,mux_array[0],mux_array[0],mux_array[0],mux_array[0],amnt[2],amnt[3]);
	

endmodule


module mux4_128$(output [127:0] Y,
		input [127:0] IN0,input [127:0] IN1, input [127:0] IN2,input [127:0] IN3,
		input S0, input S1);
genvar i;
for(i=0;i<8;i=i+1)
  begin : generate_loop
	mux4_16$(Y[i*8 +7:i*8], IN0[i*8 +7:i*8], IN1[i*8 +7:i*8], IN2[i*8 +7:i*8], IN3[i*8 +7:i*8],
			S0, S1);
  end

endmodule


module reg128e$(input CLK,
		input [127:0] Din,
		output [127:0] Q,
		output [127:0] QBAR,
		input CLR,
		input PRE,
		input en);
reg64e$ low(CLK, Din[63:0], Q[63:0], QBAR[63:0], CLR, PRE, en);
reg64e$ high(CLK, Din[127:64], Q[127:64], QBAR[127:64], CLR, PRE, en);
endmodule


