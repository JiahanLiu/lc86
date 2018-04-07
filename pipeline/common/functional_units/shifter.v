
//-------------------------------------------------------------------------------------
// shifter.v
// --------------------
// EE382N, Spring 2018
// Apruv Narkhede, Nelson Wu, Steven Flolid, Jiahan Liu
//
// shift_arithmetic_left    		- SAL with flags output          
// shift_arithmetic_right 		    - SAR with flags output          
// shift_arithmetic_left_w_carry    - SAL and outputs the last digit shifted out
// shift_arithmetic_right_w_carry   - SAR and outputs the last digit shifted out
// calculate_carry_out              - specialized logic to determine last digit carried out 
// SAR32_by_1                       - SAR 1x w/carry                 
// SAR32_by_2                       - SAR 2x w/carry                 
// SAR32_by_4                       - SAR 4x w/carry                 
// SAR32_by_8                       - SAR 8x w/carry                 
// SAR32_by_16                      - SAR 16x w/carry                
// SAL32_by_1                       - SAL 1x w/carry                 
// SAL32_by_2                       - SAL 2x w/carry                 
// SAL32_by_4                       - SAL 4x w/carry                 
// SAL32_by_8                       - SAL 8x w/carry                 
// SAL32_by_16                      - SAL 1x w/carry                 
//
//-------------------------------------------------------------------------------------
//-------------------------------------------------------------------------------------
//
// 								Shift Arthemtic Left With Carry
//
//-------------------------------------------------------------------------------------
// Functionality: SAL
//
// Combinational Delay: 
//
module shift_arithmetic_left_w_carry(
	output [31:0] sal_result,
	output carry_out, 
	input [31:0] a, b
	);
	
	wire [31:0] post_shift_1, post_shift_2, post_shift_4, post_shift_8, post_shift_16;
	wire [31:0] post_mux_1, post_mux_2, post_mux_4, post_mux_8;
	wire [4:0] leftover;

	SAL32_by_1 u_sal32_by_1(post_shift_1, leftover[0], a);
	SAL32_by_2 u_sal32_by_2(post_shift_2, leftover[1], post_mux_1);
	SAL32_by_4 u_sal32_by_4(post_shift_4, leftover[2], post_mux_2);
	SAL32_by_8 u_sal32_by_8(post_shift_8, leftover[3], post_mux_4);
	SAL32_by_16 u_sal32_by_16(post_shift_16, leftover[4], post_mux_8);

	mux32_2way u_mux_1(post_mux_1, a, post_shift_1, b[0]);
	mux32_2way u_mux_2(post_mux_2, post_mux_1, post_shift_2, b[1]);
	mux32_2way u_mux_4(post_mux_4, post_mux_2, post_shift_4, b[2]);
	mux32_2way u_mux_8(post_mux_8, post_mux_4, post_shift_8, b[3]);
	mux32_2way u_mux_16(sal_result, post_mux_8, post_shift_16, b[4]);

	calculate_carry_out u_calculate_carry_out(carry_out, b[4:0], leftover);

endmodule
//-------------------------------------------------------------------------------------
//
// 						Shift Arthemtic Right Carry with Carry
//
//-------------------------------------------------------------------------------------
// Functionality: SAR and outputs the last digit shifted out
//
// Combinational Delay: 
//
module shift_arithmetic_right_w_carry(
	output [31:0] sar_result,
	output carry_out, 
	input [31:0] a, b
	);
	
	wire [31:0] post_shift_1, post_shift_2, post_shift_4, post_shift_8, post_shift_16;
	wire [31:0] post_mux_1, post_mux_2, post_mux_4, post_mux_8;
	wire [4:0] leftover;

	SAR32_by_1 u_sar32_by_1(post_shift_1, leftover[0], a);
	SAR32_by_2 u_sar32_by_2(post_shift_2, leftover[1], post_mux_1);
	SAR32_by_4 u_sar32_by_4(post_shift_4, leftover[2], post_mux_2);
	SAR32_by_8 u_sar32_by_8(post_shift_8, leftover[3], post_mux_4);
	SAR32_by_16 u_sar32_by_16(post_shift_16, leftover[4], post_mux_8);

	mux32_2way u_mux_1(post_mux_1, a, post_shift_1, b[0]);
	mux32_2way u_mux_2(post_mux_2, post_mux_1, post_shift_2, b[1]);
	mux32_2way u_mux_4(post_mux_4, post_mux_2, post_shift_4, b[2]);
	mux32_2way u_mux_8(post_mux_8, post_mux_4, post_shift_8, b[3]);
	mux32_2way u_mux_16(sar_result, post_mux_8, post_shift_16, b[4]);

	calculate_carry_out u_calculate_carry_out(carry_out, b[4:0], leftover);
	
endmodule
//-------------------------------------------------------------------------------------
//
// 						  Shift Arthemtic Left W/ Carry
//
//-------------------------------------------------------------------------------------
// Functionality: SAL and outputs the last digit shifted out
//
// Combinational Delay: 
//
module shift_arithmetic_left(
	output [31:0] sal_result,
	input [31:0] a, b
	);
	
	wire [31:0] post_shift_1, post_shift_2, post_shift_4, post_shift_8, post_shift_16;
	wire [31:0] post_mux_1, post_mux_2, post_mux_4, post_mux_8;
	wire [4:0] leftover; //hanging wires since carry not needed

	SAL32_by_1 u_sar32_by_1(post_shift_1, leftover[0], a);
	SAL32_by_2 u_sar32_by_2(post_shift_2, leftover[1], post_mux_1);
	SAL32_by_4 u_sar32_by_4(post_shift_4, leftover[2], post_mux_2);
	SAL32_by_8 u_sar32_by_8(post_shift_8, leftover[3], post_mux_4);
	SAL32_by_16 u_sar32_by_16(post_shift_16, leftover[4], post_mux_8);

	mux32_2way u_mux_1(post_mux_1, a, post_shift_1, b[0]);
	mux32_2way u_mux_2(post_mux_2, post_mux_1, post_shift_2, b[1]);
	mux32_2way u_mux_4(post_mux_4, post_mux_2, post_shift_4, b[2]);
	mux32_2way u_mux_8(post_mux_8, post_mux_4, post_shift_8, b[3]);
	mux32_2way u_mux_16(sar_result, post_mux_8, post_shift_16, b[4]);
	
endmodule

//-------------------------------------------------------------------------------------
//
// 									Shift Arthemtic Right
//
//-------------------------------------------------------------------------------------
// Functionality: SAR and outputs the last digit shifted out
//
// Combinational Delay: 
//
module shift_arithmetic_right(
	output [31:0] sar_result,
	input [31:0] a, b
	);
	
	wire [31:0] post_shift_1, post_shift_2, post_shift_4, post_shift_8, post_shift_16;
	wire [31:0] post_mux_1, post_mux_2, post_mux_4, post_mux_8;
	wire [4:0] leftover; //hanging wires since carry not needed

	SAR32_by_1 u_sar32_by_1(post_shift_1, leftover[0], a);
	SAR32_by_2 u_sar32_by_2(post_shift_2, leftover[1], post_mux_1);
	SAR32_by_4 u_sar32_by_4(post_shift_4, leftover[2], post_mux_2);
	SAR32_by_8 u_sar32_by_8(post_shift_8, leftover[3], post_mux_4);
	SAR32_by_16 u_sar32_by_16(post_shift_16, leftover[4], post_mux_8);

	mux32_2way u_mux_1(post_mux_1, a, post_shift_1, b[0]);
	mux32_2way u_mux_2(post_mux_2, post_mux_1, post_shift_2, b[1]);
	mux32_2way u_mux_4(post_mux_4, post_mux_2, post_shift_4, b[2]);
	mux32_2way u_mux_8(post_mux_8, post_mux_4, post_shift_8, b[3]);
	mux32_2way u_mux_16(sar_result, post_mux_8, post_shift_16, b[4]);
	
endmodule
//-------------------------------------------------------------------------------------
//
// 									Calculate Carry out
//
//-------------------------------------------------------------------------------------
// Functionality: specialized logic to determine last digit carried out 
//
// Combinational Delay: 
//
module calculate_carry_out (
	output carry_out,    
	input [4:0] count_operand, 	
	input [4:0] leftover
	);

	wire enbar, pencoder_valid;
	wire [7:0] pencoder_input;
	wire [2:0] pencoder_output;

	assign enbar = 1'b0; 
	assign pencoder_input [7:5] = 3'b000;
	assign pencoder_input [4:0] = count_operand;

	pencoder8_3v$ u_pencoder(enbar, pencoder_input, pencoder_output, pencoder_valid);
	
	wire carry_that_exist;

	mux1_8way u_leftover_mux(carry_that_exist, leftover[0], leftover[1], leftover[2], 
		leftover[3], leftover[4], 1'b0, 1'b0, 1'b0, pencoder_output);
	
	mux2$ u_final_mux(carry_out, 1'b0, carry_that_exist, pencoder_valid);
endmodule

//-------------------------------------------------------------------------------------
//
// 										SAR by 1
//
//-------------------------------------------------------------------------------------
// Functionality: SAR 1x w/carry
//
// Combinational Delay: 
//
module SAR32_by_1 (
	output [31:0] out, 
	output leftover,  
	input [31:0] in
	);

	assign out [31] = in[31];
	assign out [30:0] = in[31:1];
	assign leftover = in[0];

endmodule

//-------------------------------------------------------------------------------------
//
// 										SAR by 2
//
//-------------------------------------------------------------------------------------
// Functionality: SAR 2x w/carry
//
// Combinational Delay: 
//
module SAR32_by_2 (
	output [31:0] out, 
	output leftover,  
	input [31:0] in
	);

	assign out[31:30] = {2{in[31]}};
	assign out [29:0] = in[31:2];
	assign leftover = in[1];

endmodule

//-------------------------------------------------------------------------------------
//
// 										SAR by 4
//
//-------------------------------------------------------------------------------------
// Functionality: SAR 4x w/carry
//
// Combinational Delay: 
//
module SAR32_by_4 (
	output [31:0] out, 
	output leftover,  
	input [31:0] in
	);

	assign out[31:28] = {4{in[31]}};
	assign out [27:0] = in[31:4];
	assign leftover = in[3];

endmodule

//-------------------------------------------------------------------------------------
//
// 										SAR by 8
//
//-------------------------------------------------------------------------------------
// Functionality: SAR 8x w/carry
//
// Combinational Delay: 
//
module SAR32_by_8 (
	output [31:0] out, 
	output leftover,  
	input [31:0] in
	);

	assign out[31:24] = {8{in[31]}};
	assign out [23:0] = in[31:8];
	assign leftover = in[7];

endmodule

//-------------------------------------------------------------------------------------
//
// 										SAR by 16
//
//-------------------------------------------------------------------------------------
// Functionality: SAR 16x w/carry
//
// Combinational Delay: 
//
module SAR32_by_16 (
	output [31:0] out, 
	output leftover,  
	input [31:0] in
	);

	assign out[31:16] = {16{in[31]}};
	assign out [15:0] = in[31:16];
	assign leftover = in[15];

endmodule

//-------------------------------------------------------------------------------------
//
// 										SAL by 1
//
//-------------------------------------------------------------------------------------
// Functionality: SAL 1x w/carry
//
// Combinational Delay: 
//
module SAL32_by_1 (
	output [31:0] out, 
	output leftover,  
	input [31:0] in
	);

	assign out [0] = 1'b0;
	assign out [31:1] = in[30:0];
	assign leftover = in[31];

endmodule

//-------------------------------------------------------------------------------------
//
// 										SAL by 2
//
//-------------------------------------------------------------------------------------
// Functionality: SAL 2x w/carry
//
// Combinational Delay: 
//
module SAL32_by_2 (
	output [31:0] out, 
	output leftover,  
	input [31:0] in
	);

	assign out[1:0] = 2'b00;
	assign out [31:2] = in[29:0];
	assign leftover = in[30];

endmodule

//-------------------------------------------------------------------------------------
//
// 										SAL by 4
//
//-------------------------------------------------------------------------------------
// Functionality: SAL 4x w/carry
//
// Combinational Delay: 
//
module SAL32_by_4 (
	output [31:0] out, 
	output leftover,  
	input [31:0] in
	);

	assign out[3:0] = 4'h0;
	assign out [31:4] = in[27:0];
	assign leftover = in[28];

endmodule

//-------------------------------------------------------------------------------------
//
// 										SAL by 8
//
//-------------------------------------------------------------------------------------
// Functionality: SAL 8x w/carry
//
// Combinational Delay: 
//
module SAL32_by_8 (
	output [31:0] out, 
	output leftover,  
	input [31:0] in
	);

	assign out[7:0] = 8'h00;
	assign out [31:8] = in[23:0];
	assign leftover = in[24];

endmodule

//-------------------------------------------------------------------------------------
//
// 										SAL by 16
//
//-------------------------------------------------------------------------------------
// Functionality: SAL 1x w/carry
//
// Combinational Delay: 
//
module SAL32_by_16 (
	output [31:0] out, 
	output leftover,  
	input [31:0] in
	);

	assign out[15:0] = 16'h0000;
	assign out [31:16] = in[15:0];
	assign leftover = in[16];

endmodule

