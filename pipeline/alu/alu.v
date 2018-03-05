module alu (alu_out, flags, a, b, op);
	output [31:0] alu_out;
	output [3:0] flags;
	input [31:0] a, b;
	input [2:0] op;

	wire [31:0] sum, or_result, sar_result, sal_result, pass_result, decimal_adjust_result;

	assign or_result = 32'h00000000;
	assign sal_result = 32'h00000000;
	assign sal_result = 32'h00000000;
	assign pass_result = b;

	assign decimal_adjust_result = 32'h00000000;

	adder32 alu_adder (sum, flag, a, b);

	mux32_8way out_selection(alu_out, sum, or_result, sal_result, sal_result, pass_result, decimal_adjust_result, in6, in7, op[0], op[1], op[2]);

endmodule // alu


