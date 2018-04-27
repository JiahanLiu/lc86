//-------------------------------------------------------------------------------------
//
// 					 		     = 0?
//
//-------------------------------------------------------------------------------------
// Functionality: Checks for equal to 0
//
// Combinational Delay: 
//
module equal_to_zero(
	output boolean,
	input [31:0] in
	);

	wire eq_0_3, eq_4_7, eq_8_11, eq_12_15, eq_16_19, eq_20_23, eq_24_27, eq_28_31;
	wire eq_0_15, eq_16_31;
	wire all_zero; 

	or4$ u_eq_0_3(eq_0_3, in[0], in[1], in[2], in[3]);
	or4$ u_eq_4_7(eq_4_7, in[4], in[5], in[6], in[7]);
	or4$ u_eq_8_11(eq_8_11, in[8], in[9], in[10], in[11]);
	or4$ u_eq_12_15(eq_12_15, in[12], in[13], in[14], in[15]);

	or4$ u_eq_16_19(eq_16_19, in[16], in[17], in[18], in[19]);
	or4$ u_eq_20_23(eq_20_23, in[20], in[21], in[22], in[23]);
	or4$ u_eq_24_27(eq_24_27, in[24], in[25], in[26], in[27]);
	or4$ u_eq_28_31(eq_28_31, in[28], in[29], in[30], in[31]);

	or4$ u_eq_0_15(eq_0_15, eq_0_3, eq_4_7, eq_8_11, eq_12_15);
	or4$ u_eq_16_31(eq_16_31, eq_16_19, eq_16_19, eq_24_27, eq_28_31);

	or2$ u_eq_all(all_zero, eq_0_15, eq_16_31);

	inv1$ u_boolean(boolean, all_zero);

endmodule // equal_to_zero

module equalitycheck3(
	output equal_true,
	input [2:0] a,
	input [2:0] b
	);

	wire [2:0] bit_equality;

	xnor2$ eq_0(bit_equality[0], a[0], b[0]);
	xnor2$ eq_1(bit_equality[1], a[1], b[1]);
	xnor2$ eq_2(bit_equality[2], a[2], b[2]);

	and3$ final_and(equal_true, bit_equality[0], bit_equality[1], bit_equality[2]);

endmodule // equalitycheck7

module equalitycheck7(
	output equal_true,
	input [6:0] a,
	input [6:0] b
	);

	wire [6:0] bit_equality;

	xnor2$ eq_0(bit_equality[0], a[0], b[0]);
	xnor2$ eq_1(bit_equality[1], a[1], b[1]);
	xnor2$ eq_2(bit_equality[2], a[2], b[2]);
	xnor2$ eq_3(bit_equality[3], a[3], b[3]);

	xnor2$ eq_4(bit_equality[4], a[4], b[4]);
	xnor2$ eq_5(bit_equality[5], a[5], b[5]);
	xnor2$ eq_6(bit_equality[6], a[6], b[6]);

	and1_7way final_and(equal_true, bit_equality[0], bit_equality[1], bit_equality[2],
		bit_equality[3], bit_equality[4], bit_equality[5], bit_equality[6]);

endmodule // equalitycheck7
