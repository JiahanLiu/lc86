//-------------------------------------------------------------------------------------
//
// 									  shifter32
//
//-------------------------------------------------------------------------------------
// Functionality: 32-bit Shifter
//
// Operations 0 = LEFT | 1 == RIGHT |
//
// Combinational Delay: 
//
module shifter32(
	output [31:0] shift_result,
	output [31:0] shift_flags,
	input EX_de_shift_dir_wb,
	input [31:0] a,
	input [31:0] b,
	input [1:0] datasize
	);

	wire [31:0] left_result, right_result;
	wire [31:0] left_flags, right_flags;

	shift_arithmetic_left_w_flags u_SAL(left_results, left_flags, a, b, datasize);
	shift_arithmetic_right_w_flags u_SAR(right_results, right_flags, a, b);

	mux32_2way mux_results(shift_result, left_result, right_result, EX_de_shift_dir_wb);
	mux32_2way mux_flags(shift_flags, left_flags, right_flags, EX_de_shift_dir_wb);
endmodule // shifter32	

//-------------------------------------------------------------------------------------
//
// 							Shift Arthemtic Left w/ Flags
//
//-------------------------------------------------------------------------------------
// Functionality: SAL with flags output
//
// Flags: Note that for non-zero count the AF flag is undefined, this will be 
// determined in decode since flag overwrite mask is produce in decode. 
// Also the OF flag is only affect for 1 bit shift, the overwrite mask to 
// make this happen also happens in decode. 
//
// Combinational Delay: 
//
module shift_arithmetic_left_w_flags(
	output [31:0] sal_result, flags,
	input [31:0] a, b,
	input [1:0] datasize
	);

	wire carry_out;

	shift_arithmetic_left_w_carry u_sal_carry(sal_result, carry_out, a, b, datasize);

	OF_logic u_OF_logic(OF, sal_result[31], a[31], b[31]);
	assign DF = 0; 
	assign SF = sal_result[31];
	ZF_logic u_ZF_logic(ZF, sal_result);
	assign AF = 0; //undefined
	PF_logic u_PF_logic(PF, sal_result[7:0]);
	assign CF = carry_out;

endmodule

//-------------------------------------------------------------------------------------
//
// 							Shift Arthemtic Right w/ Flags
//
//-------------------------------------------------------------------------------------
// Functionality: SAR with flags output
//
// Flags: Note that for non-zero count the AF flag is undefined, this will be 
// determined in decode since flag overwrite mask is produce in decode. 
// Also the OF flag is only affect for 1 bit shift, the overwrite mask to 
// make this happen also happens in decode. 
//
// Combinational Delay: 
//
module shift_arithmetic_right_w_flags(
	output [31:0] sar_result, flags,
	input [31:0] a, b
	);

	wire carry_out;

	shift_arithmetic_right_w_carry u_sar_carry(sar_result, carry_out, a, b);

	OF_logic u_OF_logic(OF, sar_result[31], a[31], b[31]);
	assign DF = 0; 
	assign SF = sar_result[31];
	ZF_logic u_ZF_logic(ZF, sar_result);
	assign AF = 0; //undefined
	PF_logic u_PF_logic(PF, sar_result[7:0]);
	assign CF = carry_out;

endmodule
