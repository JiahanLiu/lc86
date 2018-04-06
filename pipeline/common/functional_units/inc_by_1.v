
//-------------------------------------------------------------------------------------
// inc_by_1.v
// --------------------
// EE382N, Spring 2018
// Apruv Narkhede, Nelson Wu, Steven Flolid, Jiahan Liu
//
// inc_by_1                         - Increments a32 by 1, NO flags produced
// a_plus_carry32                   - Adds Carry32 to a32+b1         
// a_plus_carry1                    - determines sum1 based on a1+1 with carry_in1
// inc_by_1_lookahead               - Lookahead for inc_by_1 modeled after Kogge Stone
//
//-------------------------------------------------------------------------------------
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

	wire [31:0] lookahead_carry;

	inc_by_1_lookahead u_lookahead(lookahead_carry, a);

	a_plus_carry32 u_add(sum, a, lookahead_carry, 1'b1);
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

	wire [7:0] ct_level1_size4, ct_level1_size3, ct_level1_size2, ct_level1_size1;
	wire [1:0] ct_level2_size4 [3:0];
	wire [1:0] ct_level2_size3 [3:0];
	wire [1:0] ct_level2_size2 [3:0];
	wire [1:0] ct_level2_size1 [3:0];

	genvar i;
	generate
		for(i = 0; i < 8; i = i + 1)
		begin : and4_m
			and4$ and4_m (ct_level1_size4[i], a[i*4], a[i*4+1], a[i*4+2], a[i*4+3]);
		end 
	endgenerate

	genvar j;
	generate
		for(j = 0; j < 8; j = j + 1)
		begin : and3_m
			and3$ and3_m (ct_level1_size3[j], a[j*4], a[j*4+1], a[j*4+2]);
		end 
	endgenerate	


	genvar k;
	generate
		for(k = 0; k < 8; k = k + 1)
		begin : and2_m
			and2$ and2_m (ct_level1_size2[k], a[k*4], a[k*4+1]);
		end 
	endgenerate

	assign ct_level1_size1[0] = a[0];
	assign ct_level1_size1[1] = a[4];
	assign ct_level1_size1[2] = a[8];
	assign ct_level1_size1[3] = a[12];

	assign ct_level1_size1[4] = a[16];
	assign ct_level1_size1[5] = a[20];
	assign ct_level1_size1[6] = a[24];
	assign ct_level1_size1[7] = a[28]; 

	and4$ level2_size4_1 (ct_level2_size4[1], ct_level1_size4[7], ct_level1_size4[6], ct_level1_size4[5], ct_level1_size4[4]);
	and4$ level2_size4_0 (ct_level2_size4[0], ct_level1_size4[3], ct_level1_size4[2], ct_level1_size4[1], ct_level1_size4[0]);

	and3$ level2_size3_1 (ct_level2_size3[1], ct_level1_size4[6], ct_level1_size4[5], ct_level1_size4[4]);
	and3$ level2_size3_0 (ct_level2_size3[0], ct_level1_size4[2], ct_level1_size4[1], ct_level1_size4[0]);

	and2$ level2_size2_1 (ct_level2_size2[1], ct_level1_size4[5], ct_level1_size4[4]);
	and2$ level2_size2_0 (ct_level2_size2[0], ct_level1_size4[1], ct_level1_size4[0]);

	assign ct_level2_size1 [0] = ct_level1_size4[4]; 
	assign ct_level2_size1 [1] = ct_level1_size4[0];
	
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