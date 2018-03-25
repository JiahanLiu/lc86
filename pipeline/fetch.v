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


