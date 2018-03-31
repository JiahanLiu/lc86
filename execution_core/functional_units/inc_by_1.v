
//-------------------------------------------------------------------------------------
// inc_by_1.v
// --------------------
// EE382N, Spring 2018
// Apruv Narkhede, Nelson Wu, Steven Flolid, Jiahan Liu
//
// functional_unit_inc_by_1         - Increments a32 by 1, produces flags
// inc_by_1                         - Increments a32 by 1, NO flags produced
// a_plus_carry32                   - Adds Carry32 to a32+b1         
// a_plus_carry1                    - determines sum1 based on a1+1 with carry_in1
// inc_by_1_lookahead               - Lookahead for inc_by_1 modeled after Kogge Stone
//
//-------------------------------------------------------------------------------------
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
// 							   Increment by 1 (NO flags)
//
//-------------------------------------------------------------------------------------
// Functionality: Increments a32 by 1, NO flags produced
//
// Note: fastest increment by 1, same idea as Kogge Stone
//
// Combinational Delay: 4.2ns
//
module inc_by_1 (
	output [31:0] sum,
	output carry_out,
	input [31:0] a
	);

	wire [31:0] bufferedA;
	buffer32 buff_A(bufferedA, a);

	wire [31:0] lookahead_carry;

	inc_by_1_lookahead u_lookahead(lookahead_carry, bufferedA);

	a_plus_carry32 u_add(sum, bufferedA, lookahead_carry, 1'b1);
	assign carry_out = lookahead_carry[31];

endmodule

//-------------------------------------------------------------------------------------
//
// 							   Adds a32 + b1 + carry31
//
//-------------------------------------------------------------------------------------
// Functionality: Adds Carry32 to a32+b1
//
// Combinational Delay: 4.2ns
//
module a_plus_carry32 (
	output [31:0] sum,    
	input [31:0] a, 
	input [30:0] carry_found_by_lookahead,
	input b
	);
	
	a_plus_carry1 a_plus_carry1_first(sum[0], a[0], b);
	
	genvar i;
	generate
		for(i = 1; i < 32; i = i + 1)
		begin : a_plus_carry1_m
			a_plus_carry1 a_plus_carry1_m (sum[i], a[i], carry_found_by_lookahead[i-1]);
		end 
	endgenerate

endmodule

//-------------------------------------------------------------------------------------
//
// 							   Adds 1-bit a to 1 with Carry In
//
//-------------------------------------------------------------------------------------
// Functionality: determines sum1 based on a1+1 with carry_in1
//
// Combinational Delay: 4.2ns
//
module a_plus_carry1 (
	output sum,
	input a, carry_in
	);

	wire a_not, c_not;

	inv1$ not_a (a_not, a);
	inv1$ not_c (c_not, carry_in);

	wire comp1, comp2;

	and2$ and_comp1 (comp1, a, c_not);
	and2$ and_comp2 (comp2, a_not, c);

	or2$ or_final (sum, comp1, comp2);

endmodule

//-------------------------------------------------------------------------------------
//
// 							   Lookahead for increment by 1
//
//-------------------------------------------------------------------------------------
// Functionality: Lookahead for inc_by_1 modeled after Kogge Stone
//
// Combinational Delay: 4.2ns
//
module inc_by_1_lookahead (
	output [31:0] carry_found_by_lookahead,
	input [31:0] a
	);

	wire [31:0] bufferedA;
	buffer32 buffer_A(bufferedA, a);

	wire [7:0] ct_level1_size4, ct_level1_size3, ct_level1_size2, ct_level1_size1;

	genvar i;
	generate
		for(i = 0; i < 8; i = i + 1)
		begin : and4_m
			and4$ and4_m (ct_level1_size4[i], bufferedA[i*4], bufferedA[i*4+1], bufferedA[i*4+2], bufferedA[i*4+3]);
		end 
	endgenerate

	genvar j;
	generate
		for(j = 0; j < 8; j = j + 1)
		begin : and3_m
			and3$ and3_m (ct_level1_size3[j], bufferedA[j*4], bufferedA[j*4+1], bufferedA[j*4+2]);
		end 
	endgenerate	


	genvar k;
	generate
		for(k = 0; k < 8; k = k + 1)
		begin : and2_m
			and2$ and2_m (ct_level1_size2[k], bufferedA[k*4], bufferedA[k*4+1]);
		end 
	endgenerate

	assign ct_level1_size1[0] = bufferedA[0];
	assign ct_level1_size1[1] = bufferedA[4];
	assign ct_level1_size1[2] = bufferedA[8];
	assign ct_level1_size1[3] = bufferedA[12];

	assign ct_level1_size1[4] = bufferedA[16];
	assign ct_level1_size1[5] = bufferedA[20];
	assign ct_level1_size1[6] = bufferedA[24];
	assign ct_level1_size1[7] = bufferedA[28]; 


	wire [1:0] prebuff_ct_level2_size4, prebuff_ct_level2_size3, ct_level2_size2, ct_level2_size1;

	and4$ level2_size4_1 (prebuff_ct_level2_size4[1], ct_level1_size4[7], ct_level1_size4[6], ct_level1_size4[5], ct_level1_size4[4]);
	and4$ level2_size4_0 (prebuff_ct_level2_size4[0], ct_level1_size4[3], ct_level1_size4[2], ct_level1_size4[1], ct_level1_size4[0]);

	and3$ level2_size3_1 (prebuff_ct_level2_size3[1], ct_level1_size4[6], ct_level1_size4[5], ct_level1_size4[4]);
	and3$ level2_size3_0 (prebuff_ct_level2_size3[0], ct_level1_size4[2], ct_level1_size4[1], ct_level1_size4[0]);

	and2$ level2_size2_1 (ct_level2_size2[1], ct_level1_size4[5], ct_level1_size4[4]);
	and2$ level2_size2_0 (ct_level2_size2[0], ct_level1_size4[1], ct_level1_size4[0]);

	assign ct_level2_size1 [0] = ct_level1_size4[4]; 
	assign ct_level2_size1 [1] = ct_level1_size4[0];

	wire [1:0] ct_level2_size4 [3:0];
	wire [1:0] ct_level2_size3 [3:0];
							         //buff no. | high/low
	buffer32 u_level2_size4_0_buff0(ct_level2_size4[0][0], prebuff_ct_level2_size4[0]);
	buffer32 u_level2_size4_0_buff1(ct_level2_size4[1][0], prebuff_ct_level2_size4[0]);
	buffer32 u_level2_size4_0_buff2(ct_level2_size4[2][0], prebuff_ct_level2_size4[0]);
	buffer32 u_level2_size4_0_buff3(ct_level2_size4[3][0], prebuff_ct_level2_size4[0]);

	buffer32 u_level2_size4_1_buff0(ct_level2_size4[0][1], prebuff_ct_level2_size4[1]);
	buffer32 u_level2_size4_1_buff1(ct_level2_size4[1][1], prebuff_ct_level2_size4[1]);
	buffer32 u_level2_size4_1_buff2(ct_level2_size4[2][1], prebuff_ct_level2_size4[1]);
	buffer32 u_level2_size4_1_buff3(ct_level2_size4[3][1], prebuff_ct_level2_size4[1]);

	buffer32 u_level2_size3_0_buff0(ct_level2_size3[0][0], prebuff_ct_level2_size3[0]);
	buffer32 u_level2_size3_0_buff1(ct_level2_size3[1][0], prebuff_ct_level2_size3[0]);
	buffer32 u_level2_size3_0_buff2(ct_level2_size3[2][0], prebuff_ct_level2_size3[0]);
	buffer32 u_level2_size3_0_buff3(ct_level2_size3[3][0], prebuff_ct_level2_size3[0]);

	buffer32 u_level2_size3_1_buff0(ct_level2_size3[0][1], prebuff_ct_level2_size3[1]);
	buffer32 u_level2_size3_1_buff1(ct_level2_size3[1][1], prebuff_ct_level2_size3[1]);
	buffer32 u_level2_size3_1_buff2(ct_level2_size3[2][1], prebuff_ct_level2_size3[1]);
	buffer32 u_level2_size3_1_buff3(ct_level2_size3[3][1], prebuff_ct_level2_size3[1]);

	and2$ u_carry_31(carry_found_by_lookahead[31], ct_level2_size4[0][0], ct_level2_size4[0][1]);
	and3$ u_carry_30(carry_found_by_lookahead[30], ct_level2_size4[0][0], ct_level2_size3[0][1], ct_level1_size3[7]);
	and3$ u_carry_29(carry_found_by_lookahead[29], ct_level2_size4[0][0], ct_level2_size3[0][1], ct_level1_size2[7]);
	and3$ u_carry_28(carry_found_by_lookahead[28], ct_level2_size4[0][0], ct_level2_size3[0][1], ct_level1_size1[7]);

	and2$ u_carry_27(carry_found_by_lookahead[27], ct_level2_size4[1][0], ct_level2_size3[0][1]);
	and3$ u_carry_26(carry_found_by_lookahead[26], ct_level2_size4[1][0], ct_level2_size2[1], ct_level1_size3[6]);
	and3$ u_carry_25(carry_found_by_lookahead[25], ct_level2_size4[1][0], ct_level2_size2[1], ct_level1_size2[6]);
	and3$ u_carry_24(carry_found_by_lookahead[24], ct_level2_size4[1][0], ct_level2_size2[1], ct_level1_size1[6]);

	and2$ u_carry_23(carry_found_by_lookahead[23], ct_level2_size4[2][0], ct_level2_size2[1]);
	and3$ u_carry_22(carry_found_by_lookahead[22], ct_level2_size4[2][0], ct_level2_size1[1], ct_level1_size3[5]);
	and3$ u_carry_21(carry_found_by_lookahead[21], ct_level2_size4[2][0], ct_level2_size1[1], ct_level1_size2[5]);
	and3$ u_carry_20(carry_found_by_lookahead[20], ct_level2_size4[2][0], ct_level2_size1[1], ct_level1_size1[5]);

	and2$ u_carry_19(carry_found_by_lookahead[19], ct_level2_size4[3][0], ct_level2_size1[1]);
	and2$ u_carry_18(carry_found_by_lookahead[18], ct_level2_size4[3][0], ct_level1_size3[4]);
	and2$ u_carry_17(carry_found_by_lookahead[17], ct_level2_size4[3][0], ct_level1_size2[4]);
	and2$ u_carry_16(carry_found_by_lookahead[16], ct_level2_size4[3][0], ct_level1_size1[4]);

	and2$ u_carry_15(carry_found_by_lookahead[15], ct_level2_size3[0][0], ct_level1_size4[3]);
	and2$ u_carry_14(carry_found_by_lookahead[14], ct_level2_size3[0][0], ct_level1_size3[3]);
	and2$ u_carry_13(carry_found_by_lookahead[13], ct_level2_size3[0][0], ct_level1_size2[3]);
	and2$ u_carry_12(carry_found_by_lookahead[12], ct_level2_size3[0][0], ct_level1_size1[3]);

	assign carry_found_by_lookahead[11] = ct_level2_size3[1][0];
	and2$ u_carry_10(carry_found_by_lookahead[10], ct_level2_size2[0], ct_level1_size3[2]);
	and2$ u_carry_9(carry_found_by_lookahead[9], ct_level2_size2[0], ct_level1_size2[2]);
	and2$ u_carry_8(carry_found_by_lookahead[8], ct_level2_size2[0], ct_level1_size1[2]);

	assign carry_found_by_lookahead[7] = ct_level2_size2[0]; 
	and2$ u_carry_6(carry_found_by_lookahead[6], ct_level2_size1[0], ct_level1_size3[1]);
	and2$ u_carry_5(carry_found_by_lookahead[5], ct_level2_size1[0], ct_level1_size2[1]);
	and2$ u_carry_4(carry_found_by_lookahead[4], ct_level2_size1[0], ct_level1_size1[1]);

	assign carry_found_by_lookahead[3] = ct_level2_size1[0];
	assign carry_found_by_lookahead[2] = ct_level1_size3[0];
	assign carry_found_by_lookahead[1] = ct_level1_size2[0];
	assign carry_found_by_lookahead[0] = ct_level1_size1[0];

endmodule