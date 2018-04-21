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