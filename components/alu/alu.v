module alu (alu_out, flags, a, b, op);
	output [31:0] alu_out;
	output [6:0] flags;
	input [31:0] a, b;
	input [2:0] op;

	wire [31:0] adder_result, or_result, not_result, xchg_result, and_result, daa_result, cmp_result, chk_if_zero_result;
	wire [6:0] adder_flags, or_flags, not_flags, xchg_flags, and_flags, daa_flags, cmp_flags, chk_if_zero_flags;

	assign or_result = 32'h00000000;
	assign not_result = 32'h00000000;
	assign xchg_result = 32'h00000000;
	assign and_result = 32'h00000000;
	assign daa_result = 32'h00000000;
	assign cmp_result = 32'h00000000;
	assign chk_if_zero_result = 32'h00000000;

	assign or_flags = 32'h00000000;
	assign not_flags = 32'h00000000;
	assign xchg_flags = 32'h00000000;
	assign and_flags = 32'h00000000;
	assign daa_flags = 32'h00000000;
	assign cmp_flags = 32'h00000000;
	assign chk_if_zero_flags = 32'h00000000;

	adder32 alu_adder (adder_result, adder_flags, a, b);

	mux32_8way out_selection(alu_out, adder_result, or_result, not_result, xchg_result, and_result, daa_result, cmp_result, chk_if_zero_result, op[0], op[1], op[2]);
endmodule // alu

module alu_adder (sum, flags, a, b);
	output [31:0] sum;
	output [6:0] flags;
	input [31:0] a, b;

	wire carry; 

	adder32(sum, carry, a, b);  
	assign flags = 32'h00000001;
endmodule

