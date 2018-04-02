//-------------------------------------------------------------------------------------
//
// 							   Increment by 1 (YES flags)
//
//-------------------------------------------------------------------------------------
// Functionality: Increments a32 by 1, produces flags
//
// Note: Use faster module: inc_by_1 if flags aren't required 
//
// Combinational Delay: 4.2ns
//
module functional_unit_inc_by_1 (
	output [31:0] sum, 
	output [31:0] flags,
	output carry_out, 
	input [31:0] a
	);
	
	wire [31:0] internal_sum;
	wire [31:0] internal_carry_out;

	assign sum = internal_sum;
	assign carry_out = internal_carry_out;

	inc_by_1 u_inc_by_1(sum, carry_out, a);

	wire OF, DF, SF, ZF, AF, PF, CF; 

	OF_logic u_OF_logic(OF, adder_result[31], a[31], b[31]);
	assign DF = 0;
	assign SF = adder_result[31];
	ZF_logic u_ZF_logic(ZF, adder_result[31:0]);
	assign AF = internal_carry_out[3];
	PF_logic u_PF_logic(PF, adder_result[7:0]);
	assign CF = 0;

	assign_flags u_assign_flags(flags[31:0], OF, DF, SF, ZF, AF, PF, CF);	
endmodule
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
	input [31:0] a, b
	);

	wire carry_out;

	shift_arithmetic_left_w_carry(sal_result, carry_out, a, b);

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

	shift_arithmetic_right_w_carry(sar_result, carry_out, a, b);

	OF_logic u_OF_logic(OF, sar_result[31], a[31], b[31]);
	assign DF = 0; 
	assign SF = sar_result[31];
	ZF_logic u_ZF_logic(ZF, sar_result);
	assign AF = 0; //undefined
	PF_logic u_PF_logic(PF, sar_result[7:0]);
	assign CF = carry_out;

endmodule