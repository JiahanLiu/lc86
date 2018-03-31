

//-------------------------------------------------------------------------------------
// subtract.v
// --------------------
// EE382N, Spring 2018
// Apruv Narkhede, Nelson Wu, Steven Flolid, Jiahan Liu
//
// subtract32                       - subtracts a - b, then sets flags
//
//-------------------------------------------------------------------------------------
//-------------------------------------------------------------------------------------
//
// 									 32-bit Subtract
//
//-------------------------------------------------------------------------------------
// Functionality: subtracts a - b, then sets flags
//
// Combinational Delay: 4.2ns
//
module subtract32 (
	output [31:0] difference, carry_out,  
	input [31:0] a, b
	);

	wire [31:0] b_not;
	wire carry_in;

	not32_1way u_not_b(b_not, b);

	adder32_w_carry_in adder32_w_carry_in(difference, carry_out, a, b_not, 1'b1);

endmodule
