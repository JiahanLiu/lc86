
//-------------------------------------------------------------------------------------
// muxes.v
// --------------------
// EE382N, Spring 2018
// Apruv Narkhede, Nelson Wu, Steven Flolid, Jiahan Liu
//
// mux1_8way                        - 1-bit Mux with 8 inputs        
// mux32_2way                       - 32-bit Mux with 2 inputs       
// mux32_4way                       - 32-bit Mux with 4 inputs       
// mux32_8way                       - 32-bit Mux with 8 inputs       
//
//-------------------------------------------------------------------------------------

//-------------------------------------------------------------------------------------
//
// 					 		    1-bit Mux with 8 inputs
//
//-------------------------------------------------------------------------------------
// Functionality: 1-bit Mux with 8 inputs
//
// Combinational Delay: 
//
module mux1_8way(
	output mux_out,
	input a, b, c, d, e, f, g, h,
	input [2:0] select
	);

	wire low_result, high_result;

	mux4$ u_mux_low(low_result, a, b, c, d, select[1], select[0]);	
	mux4$ u_mux_high(high_result, e, f, g, h, select[1], select[0]);

	mux2$ u_mux_final(mux_out, low_result, high_result, select[2]); 

endmodule

//-------------------------------------------------------------------------------------
//
// 					 		    32-bit Mux with 2 inputs
//
//-------------------------------------------------------------------------------------
// Functionality: 32-bit Mux with 2 inputs
//
// Combinational Delay: 
//
module mux32_2way(
	output [31:0] mux_out,
	input [31:0] a, b,
	input select
	);

	mux2_16$ high(mux_out[31:16], a[31:16], b[31:16], select);
	mux2_16$ low(mux_out[15:0], a[15:0], b[15:0], select);

endmodule // mux32_2way

//-------------------------------------------------------------------------------------
//
// 					 		    32-bit Mux with 3 inputs
//
//-------------------------------------------------------------------------------------
// Functionality: 32-bit Mux with 3 inputs
//
// Combinational Delay: 
//
module mux32_3way (
	output [31:0] mux_out,
	input [31:0] a, b, c,
	input [1:0] select
	);

	mux3_16$ u_high(mux_out[31:16], a[31:16], b[31:16], c[31:16], select[0], select[1]);
	mux3_16$ u_low(mux_out[15:0], a[15:0], b[15:0], c[15:0], select[0], select[1]);

endmodule

//-------------------------------------------------------------------------------------
//
// 					 		    32-bit Mux with 4 inputs
//
//-------------------------------------------------------------------------------------
// Functionality: 32-bit Mux with 4 inputs
//
// Combinational Delay: 
//
module mux32_4way(
	output [31:0] mux_out, 
	input [31:0] a, b, c, d,
	input [1:0] select);

	mux4_16$ high(mux_out[31:16], a[31:16], b[31:16], c[31:16], d[31:16], select[0], select[1]);
	mux4_16$ low(mux_out[15:0], a[15:0], b[15:0], c[15:0], d[15:0], select[0], select[1]);

endmodule // mux32_4way


//-------------------------------------------------------------------------------------
//
// 					 		    32-bit Mux with 8 inputs
//
//-------------------------------------------------------------------------------------
// Functionality: 32-bit Mux with 8 inputs
//
// Combinational Delay: 
//
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
