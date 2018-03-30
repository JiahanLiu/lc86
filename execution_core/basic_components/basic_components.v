module assign_wire1(
	output out,
	input in
	);

	assign out = in;

endmodule

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

