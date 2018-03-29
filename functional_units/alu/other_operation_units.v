module subtract32 (
	output [31:0] difference, carry_out,  
	input [31:0] a, b
);

	wire [31:0] b_not;
	wire carry_in;

	not32_2way u_not_b(b_not, b);

	adder32 adder32_w_carry_in(difference, carry_out, a, b_not, 1'b1);

endmodule