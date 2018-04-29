
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
	input [31:0] a, b,
	input [1:0] datasize
	);
	
	wire [31:0] post_shift_1, post_shift_2, post_shift_4, post_shift_8, post_shift_16;
	wire [31:0] post_mux_1, post_mux_2, post_mux_4, post_mux_8;
	wire CF_size_32, CF_size_16, CF_size_8;  

	SAL32_by_1 u_sal32_by_1(post_shift_1, a, datasize);
	SAL32_by_2 u_sal32_by_2(post_shift_2, post_mux_1, datasize);
	SAL32_by_4 u_sal32_by_4(post_shift_4, post_mux_2, datasize);
	SAL32_by_8 u_sal32_by_8(post_shift_8, post_mux_4, datasize);
	SAL32_by_16 u_sal32_by_16(post_shift_16, post_mux_8, datasize);

	mux32_2way u_mux_1(post_mux_1, a, post_shift_1, b[0]);
	mux32_2way u_mux_2(post_mux_2, post_mux_1, post_shift_2, b[1]);
	mux32_2way u_mux_4(post_mux_4, post_mux_2, post_shift_4, b[2]);
	mux32_2way u_mux_8(post_mux_8, post_mux_4, post_shift_8, b[3]);
	mux32_2way u_mux_16(sal_result, post_mux_8, post_shift_16, b[4]);

	CF_flag_shift_left u_CF_flag_shift_left32(CF_size_32, a, b[4:0]); 
	CF_flag_shift_left u_CF_flag_shift_left16(CF_size_16, {a[15:0], {16{1'b0}}}, b[4:0]); 
	CF_flag_shift_left u_CF_flag_shift_left8(CF_size_8, {a[7:0], {24{1'b0}}}, b[4:0]); 

	mux3$ u_mux_CF(carry_out, CF_size_8, CF_size_16, CF_size_32, datasize[0], datasize[1]);

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
	input [31:0] a, b, 
	input [1:0] datasize
	);
	
	wire [31:0] post_shift_1, post_shift_2, post_shift_4, post_shift_8, post_shift_16;
	wire [31:0] post_mux_1, post_mux_2, post_mux_4, post_mux_8;
	wire CF_size_32, CF_size_16, CF_size_8;  

	SAR32_by_1 u_sar32_by_1(post_shift_1, a);
	SAR32_by_2 u_sar32_by_2(post_shift_2, post_mux_1);
	SAR32_by_4 u_sar32_by_4(post_shift_4, post_mux_2);
	SAR32_by_8 u_sar32_by_8(post_shift_8, post_mux_4);
	SAR32_by_16 u_sar32_by_16(post_shift_16, post_mux_8);

	mux32_2way u_mux_1(post_mux_1, a, post_shift_1, b[0]);
	mux32_2way u_mux_2(post_mux_2, post_mux_1, post_shift_2, b[1]);
	mux32_2way u_mux_4(post_mux_4, post_mux_2, post_shift_4, b[2]);
	mux32_2way u_mux_8(post_mux_8, post_mux_4, post_shift_8, b[3]);
	mux32_2way u_mux_16(sar_result, post_mux_8, post_shift_16, b[4]);

	CF_flag_shift_right u_CF_flag_shift_right32(CF_size_32, a, b[4:0]); 
	CF_flag_shift_right u_CF_flag_shift_right16(CF_size_16, {a[15:0], {16{1'b0}}}, b[4:0]); 
	CF_flag_shift_right u_CF_flag_shift_right8(CF_size_8, {a[7:0], {24{1'b0}}}, b[4:0]); 

	mux3$ u_mux_CF(carry_out, CF_size_8, CF_size_16, CF_size_32, datasize[0], datasize[1]);
	
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

	SAL32_by_1 u_sar32_by_1(post_shift_1,  a, 2'b00);
	SAL32_by_2 u_sar32_by_2(post_shift_2, post_mux_1, 2'b00);
	SAL32_by_4 u_sar32_by_4(post_shift_4, post_mux_2, 2'b00);
	SAL32_by_8 u_sar32_by_8(post_shift_8, post_mux_4, 2'b00);
	SAL32_by_16 u_sar32_by_16(post_shift_16, post_mux_8, 2'b00);

	mux32_2way u_mux_1(post_mux_1, a, post_shift_1, b[0]);
	mux32_2way u_mux_2(post_mux_2, post_mux_1, post_shift_2, b[1]);
	mux32_2way u_mux_4(post_mux_4, post_mux_2, post_shift_4, b[2]);
	mux32_2way u_mux_8(post_mux_8, post_mux_4, post_shift_8, b[3]);
	mux32_2way u_mux_16(sal_result, post_mux_8, post_shift_16, b[4]);
	
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

	SAR32_by_1 u_sar32_by_1(post_shift_1, a);
	SAR32_by_2 u_sar32_by_2(post_shift_2, post_mux_1);
	SAR32_by_4 u_sar32_by_4(post_shift_4, post_mux_2);
	SAR32_by_8 u_sar32_by_8(post_shift_8, post_mux_4);
	SAR32_by_16 u_sar32_by_16(post_shift_16, post_mux_8);

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
	input [31:0] in
	);

	assign out [31] = in[31];
	assign out [30:0] = in[31:1];

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
	input [31:0] in
	);

	assign out[31:30] = {2{in[31]}};
	assign out [29:0] = in[31:2];

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
	input [31:0] in
	);

	assign out[31:28] = {4{in[31]}};
	assign out [27:0] = in[31:4];

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
	input [31:0] in
	);

	assign out[31:24] = {8{in[31]}};
	assign out [23:0] = in[31:8];

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
	input [31:0] in
	);

	assign out[31:16] = {16{in[31]}};
	assign out [15:0] = in[31:16];

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
	input [31:0] in,
	input [1:0] datasize
	);

	assign out [0] = 1'b0;
	assign out [31:1] = in[30:0];
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
	input [31:0] in,
	input [1:0] datasize
	);

	assign out[1:0] = 2'b00;
	assign out [31:2] = in[29:0];

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
	input [31:0] in,
	input [1:0] datasize
	);

	assign out[3:0] = 4'h0;
	assign out [31:4] = in[27:0];
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
	input [31:0] in,
	input [1:0] datasize
	);


	assign out[7:0] = 8'h00;
	assign out [31:8] = in[23:0];

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
	input [31:0] in,
	input [1:0] datasize
	);

	assign out[15:0] = 16'h0000;
	assign out [31:16] = in[15:0];

endmodule

//-------------------------------------------------------------------------------------
//
// 					 		    1-bit Mux with 32 inputs
//
//-------------------------------------------------------------------------------------
// Functionality: 1-bit Mux with 32 inputs
//
// Combinational Delay: 
//
module CF_flag_shift_right(
	output CF,
	input [31:0] a,
	input [4:0] select
	);

	wire result0, result1, result2, result3;

	mux1_8way u_mux1_8way0(result0, a[0], a[0], a[1], a[2], a[3], a[4], a[5], a[6], select[2:0]);
	mux1_8way u_mux1_8way1(result1, a[7], a[8], a[9], a[10], a[11], a[12], a[13], a[14], select[2:0]);
	mux1_8way u_mux1_8way2(result2, a[15], a[16], a[17], a[18], a[19], a[20], a[21], a[22], select[2:0]);
	mux1_8way u_mux1_8way3(result3, a[23], a[24], a[25], a[26], a[27], a[28], a[29], a[30], select[2:0]);

	mux4$ u_mux_final(CF, result0, result1, result2, result3, select[4], select[3]);	

endmodule

//-------------------------------------------------------------------------------------
//
// 					 		    1-bit Mux with 32 inputs
//
//-------------------------------------------------------------------------------------
// Functionality: 1-bit Mux with 32 inputs
//
// Combinational Delay: 
//
module CF_flag_shift_left(
	output CF,
	input [31:0] a,
	input [4:0] select
	);

	wire result0, result1, result2, result3;

	mux1_8way u_mux1_8way0(result0, a[31], a[31], a[30], a[29], a[28], a[27], a[26], a[25], select[2:0]);
	mux1_8way u_mux1_8way1(result1, a[24], a[23], a[22], a[21], a[20], a[19], a[18], a[17], select[2:0]);
	mux1_8way u_mux1_8way2(result2, a[16], a[15], a[14], a[13], a[12], a[11], a[10], a[9], select[2:0]);
	mux1_8way u_mux1_8way3(result3, a[8], a[7], a[6], a[5], a[4], a[3], a[2], a[1], select[2:0]);

	mux4$ u_mux_final(CF, result0, result1, result2, result3, select[3], select[4]);	

endmodule
