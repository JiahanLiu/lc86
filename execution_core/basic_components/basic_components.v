module assign_wire1(
	output out,
	input in
	);

	assign out = in;

endmodule

module mux32_8way(
	output [31:0] mux_out,
	input [31:0] a, b, c, d, e, f, g, h,
	input [2:0] select
	);

	wire [31:0] low_result, high_result;

	mux32_4way low_choices(low_result, a, b, c, d, select[1:0]);
	mux32_4way high_choices(high_result, e, f, g, h, select[1:0]);

	mux32_2way final_choices(mux_out, low_result, high_result, select[2]);

endmodule // mux32_8way

module mux32_4way (
	output [31:0] mux_out, 
	input [31:0] a, b, c, d,
	input [1:0] select);

	mux4_16$ high(mux_out[31:16], a[31:16], b[31:16], c[31:16], d[31:16], select[0], select[1]);
	mux4_16$ low(mux_out[15:0], a[15:0], b[15:0], c[15:0], d[15:0], select[0], select[1]);

endmodule // mux32_4way

module mux32_2way (
	output [31:0] mux_out,
	input [31:0] a, b,
	input select
	);

	mux2_16$ high(mux_out[31:16], a[31:16], b[31:16], select);
	mux2_16$ low(mux_out[15:0], a[15:0], b[15:0], select);

endmodule // mux32_2way

module or32_2way (
	output [31:0] or_out, 
	input [31:0] a,
	input [31:0] b
	);

	genvar i;
	generate
		for(i = 0; i < 32; i = i + 1)
		begin : u_or
			or2$ u_or (or_out[i], a[i], b[i]);
		end 
	endgenerate

endmodule

module and32_2way (
	output [31:0] and_out, 
	input [31:0] a,
	input [31:0] b
	);

	genvar i;
	generate
		for(i = 0; i < 32; i = i + 1)
		begin : u_and
			and2$ u_and (and_out[i], a[i], b[i]);
		end 
	endgenerate

endmodule

module not32_2way (
	output [31:0] not_out, 
	input [31:0] a
	);

	genvar i;
	generate
		for(i = 0; i < 32; i = i + 1)
		begin : u_not
			inv1$ u_not (not_out[i], a[i]);
		end 
	endgenerate

endmodule

module not4_2way (
	output [3:0] not_out,
	input [3:0] a
	);

	genvar i;
	generate
		for(i = 0; i < 4; i = i + 1)
		begin : u_not
			inv1$ u_not (not_out[i], a[i]);
		end 
	endgenerate	

endmodule

module and1_5way (
	output and_out,
	input a, b, c, d, e
	);

	wire intermediate_3side, intermediate_2side;

	and3$ u_and_intermediate3 (intermediate_3side, a, b, c);
	and2$ u_and_intermedaite2 (intermediate_2side, d, e);

	and2$ u_and_final (and_out, intermediate_3side, intermediate_2side);

endmodule

module or1_5way (
	output or_out,
	input a, b, c, d, e
	);

	wire intermediate_3side, intermediate_2side;

	or3$ u_or_intermediate3 (intermediate_3side, a, b, c);
	or2$ u_or_intermedaite2 (intermediate_2side, d, e);

	or2$ u_or_final (or_out, intermediate_3side, intermediate_2side);

endmodule

module or1_6way (
	output or_out,
	input a, b, c, d, e, f
	);

	wire intermediate_3side_1, intermediate_3side_2;

	or3$ u_or_intermediate3_1 (intermediate_3side_1, a, b, c);
	or3$ u_or_intermedaite3_2 (intermediate_3side_2, d, e, f);

	or2$ u_or_final (or_out, intermediate_3side_1, intermediate_3side_2);

endmodule

module buffer32 (
	output [31:0] out,
	input [31:0] in
	);

	buffer16$ u_buffu_high(out[31:16], in[31:16]);
	buffer16$ u_buff_low(out[15:0], in[15:0]);

endmodule



