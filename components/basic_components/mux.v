module mux32_8way(mux_out, in0, in1, in2, in3, in4, in5, in6, in7, s0, s1, s2);
	output [31:0] mux_out;
	input [31:0] in0, in1, in2, in3, in4, in5, in6, in7;
	input s0, s1, s2;

	wire [31:0] low_result;
	wire [31:0] high_result;

	mux32_4way low_choices(low_result, in0, in1, in2, in3, s0, s1);
	mux32_4way high_choices(high_result, in4, in5, in6, in7, s0, s1);

	mux32_2way final_choices(mux_out, low_result, high_result, s2);

endmodule // mux32_8way

module mux32_4way (mux_out, in0, in1, in2, in3, s0, s1);
	output [31:0] mux_out;
	input [31:0] in0, in1, in2, in3;
	input s0, s1;

	mux4_16$ high(mux_out[31:16], in0[31:16], in1[31:16], in2[31:16], in3[31:16], s0, s1);
	mux4_16$ low(mux_out[15:0], in0[15:0], in1[15:0], in2[15:0], in3[15:0], s0, s1);

endmodule // mux32_4way

module mux32_2way (mux_out, in0, in1, s0);
	output [31:0] mux_out;
	input [31:0] in0, in1;
	input s0;

	mux2_16$ high(mux_out[31:16], in0[31:16], in1[31:16], s0);
	mux2_16$ low(mux_out[15:0], in0[15:0], in1[15:0], s0);

endmodule // mux32_2way