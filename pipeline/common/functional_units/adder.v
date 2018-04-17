//-------------------------------------------------------------------------------------
// adder.v
// --------------------
// EE382N, Spring 2018
// Apruv Narkhede, Nelson Wu, Steven Flolid, Jiahan Liu
//
// adder32                          - Fastest adder (NO flags, NO carry in)
// adder32_w_carry_in               - Adder (NO flags, YES carry in) 
// sum1                             - sums a1, b1, c1                
// sum32                            - sums a32, b32, carry32, carryin
// propagate1                       - Can a carry possibily propgate?
// propagate32                      - Propagate bits32 given a32, b32
// generate1                        - Generate carry immediately?    
// generate32                       - Generate bits32 given a32, b32 
// propagate1_w_carry_in            - Propagate1 with carry in       
// propagate32_w_carry_in           - Propagate32 with carry in      
// generate1_w_carry_in             - Generate1 with carry in        
// generate32_w_carry_in            - Generate32 bits32 given a32, b32
// gp_group1                        - Single Kogge Stone unit        
// gp_group32                       - Kogge-Stone Carry Look Ahead 32 bits
//
//-------------------------------------------------------------------------------------

//-------------------------------------------------------------------------------------
//
// 					Kogge Stone 32-bit Adder, NO flags, NO carry in
//
//-------------------------------------------------------------------------------------
// Functionality: Fastest adder (NO flags, NO carry in)
//
// Combinational Delay: 4.2ns
//
module adder32(sum, carry_out, a, b);
	output [31:0] sum;
	output [31:0] carry_out; 
	input [31:0] a,b;
	wire carry_in;

	assign carry_in = 0; 

	wire [31:0] propagate32_result, generate32_result, internal_carry;

	generate32 generate32_m (generate32_result, a, b);
  	propagate32 propagate32_m (propagate32_result, a, b);
   	gp_group32 kogge_stone_lookahead (internal_carry, generate32_result, propagate32_result);
   	sum32 sum32_m (sum, a, b, internal_carry, carry_in);

   	assign carry_out = internal_carry;

endmodule

//-------------------------------------------------------------------------------------
//
// 				 Kogge Stone 32-bit Adder, NO flags, YES carry in
//
//-------------------------------------------------------------------------------------
// Functionality: Adder (NO flags, YES carry in)
//
// Combinational Delay: ~4.4ns
//
module adder32_w_carry_in(sum, carry_out, a, b, carry_in);
	output [31:0] sum;
	output [31:0] carry_out; 
	input [31:0] a,b;
	input carry_in;


	wire [31:0] propagate32_result, generate32_result, internal_carry;

	generate32_w_carry_in generate32_m (generate32_result, a, b, carry_in);
  	propagate32_w_carry_in propagate32_m (propagate32_result, a, b, carry_in);
   	gp_group32 kogge_stone_lookahead (internal_carry, generate32_result, propagate32_result);
   	sum32 sum32_m (sum, a, b, internal_carry, carry_in);

   	assign carry_out = internal_carry;

endmodule

//-------------------------------------------------------------------------------------
//
// 									  1-bit Adder
//
//-------------------------------------------------------------------------------------
// Functionality: sums a1, b1, c1
//
// Combinational Delay: 1.0ns
//

module sum1 (sum, a, b, c);
	output sum;
	input a, b, c;

	wire a_not, b_not, c_not;
	wire a_asserted, b_asserted, c_asserted, all_asserted;

	inv1$ not_a (a_not, a);
	inv1$ not_b (b_not, b);
	inv1$ not_c (c_not, c);

	and3$ and_a_asserted (a_asserted, a, b_not, c_not);
	and3$ and_b_asserted (b_asserted, a_not, b, c_not);
	and3$ and_c_asserted (c_asserted, a_not, b_not, c);
	and3$ and_all_asserted (all_asserted, a, b, c);
	or4$ or_asserted (sum, a_asserted, b_asserted, c_asserted, all_asserted);

endmodule // sum1

//-------------------------------------------------------------------------------------
//
// 									32-bit Adder 
//
//-------------------------------------------------------------------------------------
// Functionality: sums a32, b32, carry32, carryin
//
// Combinational Delay: 1.0ns
//

module sum32 (sum, a, b, c, carry_in);
	output [31:0] sum;
	input [31:0] a, b, c;
	input carry_in;

	sum1 sum1_0 (sum[0], a[0], b[0], carry_in);
	
	genvar i;
	generate
		for(i = 1; i < 32; i = i + 1)
		begin : sum_m
			sum1 sum1_m (sum[i], a[i], b[i], c[i-1]);
		end 
	endgenerate

endmodule // sum32

//-------------------------------------------------------------------------------------
//
// 									1-bit Propgate
//
//-------------------------------------------------------------------------------------
// Functionality: Can a carry possibily propgate?
//
// Combinational Delay: 0.35ns, tested 0.36ns
//

module propagate1 (p, a, b);
	output p;
	input a, b;

	or2$ or_to_p (p, a, b);

endmodule // propagate1

//-------------------------------------------------------------------------------------
//
// 									32-bit Propgate
//
//-------------------------------------------------------------------------------------
// Functionality: Propagate bits32 given a32, b32
//
// Combinational Delay: 0.35ns, tested 0.36ns
//

module propagate32 (p, a, b);
	output [31:0] p;
	input [31:0] a, b;

	genvar i;
	generate
		for(i = 0; i < 32; i = i + 1)
		begin : propagate_m
			propagate1 propagate_m (p[i], a[i], b[i]);
		end 
	endgenerate

endmodule // propagate32

//-------------------------------------------------------------------------------------
//
// 									1-bit Generate
//
//-------------------------------------------------------------------------------------
// Functionality: Generate carry immediately?
//
// Combinational Delay: 0.35ns
//

module generate1 (g, a, b);
	output g;
	input a, b;

	and2$ and_to_g (g, a, b);

endmodule // generate1

//-------------------------------------------------------------------------------------
//
// 									32-bit Generate
//
//-------------------------------------------------------------------------------------
// Functionality: Generate bits32 given a32, b32
//
// Combinational Delay: 0.35ns
//

module generate32 (g, a, b);
	output [31:0] g;
	input [31:0] a, b;

	genvar i;
	generate 
		for(i = 0; i < 32; i = i + 1)
		begin : generate1_m
			generate1 generate1_m (g[i], a[i], b[i]);
		end
	endgenerate

endmodule // generate32

//-------------------------------------------------------------------------------------
//
// 							 1-bit Propgate, YES carry in
//
//-------------------------------------------------------------------------------------
// Functionality: Propagate1 with carry in
//
// Combinational Delay: 0.35ns, tested 0.36ns
//
module propagate1_w_carry_in (p, a, b, carry_in);
	output p;
	input a, b, carry_in;

	or3$ or_to_p (p, a, b, carry_in);

endmodule

//-------------------------------------------------------------------------------------
//
// 						    32-bit Propagate, YES Carry In
//
//-------------------------------------------------------------------------------------
// Functionality: Propagate32 with carry in 
//
// Combinational Delay: 0.35ns, tested 0.36ns
//

module propagate32_w_carry_in (p, a, b, carry_in);
	output [31:0] p;
	input [31:0] a, b;
	input carry_in;

	propagate1_w_carry_in u_first_propagate(p[0], a[0], b[0], carry_in);

	genvar i;
	generate
		for(i = 1; i < 32; i = i + 1)
		begin : propagate_m
			propagate1 propagate_m (p[i], a[i], b[i]);
		end 
	endgenerate

endmodule 

//-------------------------------------------------------------------------------------
//
// 							1-bit Generate with Carry In
//
//-------------------------------------------------------------------------------------
// Functionality: Generate1 with carry in
//
// Combinational Delay: 0.35ns
//

module generate1_w_carry_in (g, a, b, carry_in);
	output g;
	input a, b, carry_in;

	wire a_b_comp, a_c_comp, b_c_comp;

	and2$ u_and_a_b(a_b_comp, a, b);
	and2$ u_and_a_c(a_c_comp, a, carry_in);
	and2$ u_and_b_c(b_c_comp, b, carry_in);

	or3$ and_to_g (g, a_b_comp, a_c_comp, b_c_comp);

endmodule 

//-------------------------------------------------------------------------------------
//
// 							32-bit Generate with Carry In
//
//-------------------------------------------------------------------------------------
// Functionality: Generate32 bits32 given a32, b32
//
// Combinational Delay: 0.35ns
//

module generate32_w_carry_in (g, a, b, carry_in);
	output [31:0] g;
	input [31:0] a, b;
	input carry_in;

	generate1_w_carry_in u_first_generate(g[0], a[0], b[0], carry_in);

	genvar i;
	generate 
		for(i = 1; i < 32; i = i + 1)
		begin : generate1_m
			generate1 generate1_m (g[i], a[i], b[i]);
		end
	endgenerate

endmodule // generate32

//-------------------------------------------------------------------------------------
//
// 							1-bit Generate_Propagate_Group
//
//-------------------------------------------------------------------------------------
// Functionality: Single Kogge Stone unit
//
// Combinational Delay: 0.7ns theory -> 0.71 actual
//

module gp_group1 (g_out, p_out, g_in_high, p_in_high, g_in_low, p_in_low);
	output g_out, p_out;
	input g_in_high, p_in_high, g_in_low, p_in_low;

	wire prev_generate;

	and2$ and_to_propagate (p_out, p_in_low, p_in_high);
	and2$ and_prev_generate (prev_generate, g_in_low, p_in_high);
	or2$ or_to_generate (g_out, prev_generate, g_in_high);

endmodule // gp_group1

//-------------------------------------------------------------------------------------
//
// 							32-bit Generate_Propagate_Group 
//
//-------------------------------------------------------------------------------------
// Functionality: Kogge-Stone Carry Look Ahead 32 bits
//
// Combinational Delay: eta 7ns?
//

module gp_group32 (c, g, p);
	output [31:0] c;
	input [31:0] g, p;


	wire [31:1] wire_r0_g, wire_r0_p; //low index go straight to carry
	wire [31:2] wire_r1_g, wire_r1_p;
	wire [31:4] wire_r2_g, wire_r2_p;
	wire [31:8] wire_r3_g, wire_r3_p;
	wire [31:16] trash_propagate;

	assign c[0] = g[0];

		//row 0
	//sample gp_r0_30(g_out, p_out, g_in_high, p_in_high, g_in_low, p_in_low);
	gp_group1 gp_r0_31(wire_r0_g[31], wire_r0_p[31], g[31], p[31], g[30], p[30]);
	gp_group1 gp_r0_30(wire_r0_g[30], wire_r0_p[30], g[30], p[30], g[29], p[29]);
	gp_group1 gp_r0_29(wire_r0_g[29], wire_r0_p[29], g[29], p[29], g[28], p[28]);
	gp_group1 gp_r0_28(wire_r0_g[28], wire_r0_p[28], g[28], p[28], g[27], p[27]);
	gp_group1 gp_r0_27(wire_r0_g[27], wire_r0_p[27], g[27], p[27], g[26], p[26]);
	gp_group1 gp_r0_26(wire_r0_g[26], wire_r0_p[26], g[26], p[26], g[25], p[25]);
	gp_group1 gp_r0_25(wire_r0_g[25], wire_r0_p[25], g[25], p[25], g[24], p[24]);
	gp_group1 gp_r0_24(wire_r0_g[24], wire_r0_p[24], g[24], p[24], g[23], p[23]);
	//sample gp_r0_30(wire_r0_g[31], wire_r0_p[31], g_in_high, p_in_high, g_in_low, p_in_low);
	gp_group1 gp_r0_23(wire_r0_g[23], wire_r0_p[23], g[23], p[23], g[22], p[22]);
	gp_group1 gp_r0_22(wire_r0_g[22], wire_r0_p[22], g[22], p[22], g[21], p[21]);
	gp_group1 gp_r0_21(wire_r0_g[21], wire_r0_p[21], g[21], p[21], g[20], p[20]);
	gp_group1 gp_r0_20(wire_r0_g[20], wire_r0_p[20], g[20], p[20], g[19], p[19]);
	gp_group1 gp_r0_19(wire_r0_g[19], wire_r0_p[19], g[19], p[19], g[18], p[18]);
	gp_group1 gp_r0_18(wire_r0_g[18], wire_r0_p[18], g[18], p[18], g[17], p[17]);
	gp_group1 gp_r0_17(wire_r0_g[17], wire_r0_p[17], g[17], p[17], g[16], p[16]);
	gp_group1 gp_r0_16(wire_r0_g[16], wire_r0_p[16], g[16], p[16], g[15], p[15]);
	//sample gp_r0_30(wire_r0_g[31], wire_r0_p[31], g_in_high, p_in_high, g_in_low, p_in_low);
	gp_group1 gp_r0_15(wire_r0_g[15], wire_r0_p[15], g[15], p[15], g[14], p[14]);
	gp_group1 gp_r0_14(wire_r0_g[14], wire_r0_p[14], g[14], p[14], g[13], p[13]);
	gp_group1 gp_r0_13(wire_r0_g[13], wire_r0_p[13], g[13], p[13], g[12], p[12]);
	gp_group1 gp_r0_12(wire_r0_g[12], wire_r0_p[12], g[12], p[12], g[11], p[11]);
	gp_group1 gp_r0_11(wire_r0_g[11], wire_r0_p[11], g[11], p[11], g[10], p[10]);
	gp_group1 gp_r0_10(wire_r0_g[10], wire_r0_p[10], g[10], p[10], g[9], p[9]);
	gp_group1 gp_r0_9(wire_r0_g[9], wire_r0_p[9], g[9], p[9], g[8], p[8]);
	gp_group1 gp_r0_8(wire_r0_g[8], wire_r0_p[8], g[8], p[8], g[7], p[7]);
	//sample gp_r0_30(wire_r0_g[31], wire_r0_p[31], g_in_high, p_in_high, g_in_low, p_in_low);
	gp_group1 gp_r0_7(wire_r0_g[7], wire_r0_p[7], g[7], p[7], g[6], p[6]);
	gp_group1 gp_r0_6(wire_r0_g[6], wire_r0_p[6], g[6], p[6], g[5], p[5]);
	gp_group1 gp_r0_5(wire_r0_g[5], wire_r0_p[5], g[5], p[5], g[4], p[4]);
	gp_group1 gp_r0_4(wire_r0_g[4], wire_r0_p[4], g[4], p[4], g[3], p[3]);
	gp_group1 gp_r0_3(wire_r0_g[3], wire_r0_p[3], g[3], p[3], g[2], p[2]);
	gp_group1 gp_r0_2(wire_r0_g[2], wire_r0_p[2], g[2], p[2], g[1], p[1]);
	gp_group1 gp_r0_1(wire_r0_g[1], wire_r0_p[1], g[1], p[1], g[0], p[0]);

	assign c[1] = wire_r0_g[1];

		//row 1
	//sample gp_r0_30(g_out, p_out, g_in_high, p_in_high, g_in_low, p_in_low);
	gp_group1 gp_r1_31(wire_r1_g[31], wire_r1_p[31], wire_r0_g[31], wire_r0_p[31], wire_r0_g[29], wire_r0_p[29]);
	gp_group1 gp_r1_30(wire_r1_g[30], wire_r1_p[30], wire_r0_g[30], wire_r0_p[30], wire_r0_g[28], wire_r0_p[28]);
	gp_group1 gp_r1_29(wire_r1_g[29], wire_r1_p[29], wire_r0_g[29], wire_r0_p[29], wire_r0_g[27], wire_r0_p[27]);
	gp_group1 gp_r1_28(wire_r1_g[28], wire_r1_p[28], wire_r0_g[28], wire_r0_p[28], wire_r0_g[26], wire_r0_p[26]);
	gp_group1 gp_r1_27(wire_r1_g[27], wire_r1_p[27], wire_r0_g[27], wire_r0_p[27], wire_r0_g[25], wire_r0_p[25]);
	gp_group1 gp_r1_26(wire_r1_g[26], wire_r1_p[26], wire_r0_g[26], wire_r0_p[26], wire_r0_g[24], wire_r0_p[24]);
	gp_group1 gp_r1_25(wire_r1_g[25], wire_r1_p[25], wire_r0_g[25], wire_r0_p[25], wire_r0_g[23], wire_r0_p[23]);
	gp_group1 gp_r1_24(wire_r1_g[24], wire_r1_p[24], wire_r0_g[24], wire_r0_p[24], wire_r0_g[22], wire_r0_p[22]);
	//sample gp_r1_30(wire_r1_g[31], wire_r1_p[31], g_in_high, p_in_high, g_in_low, p_in_low);
	gp_group1 gp_r1_23(wire_r1_g[23], wire_r1_p[23], wire_r0_g[23], wire_r0_p[23], wire_r0_g[21], wire_r0_p[21]);
	gp_group1 gp_r1_22(wire_r1_g[22], wire_r1_p[22], wire_r0_g[22], wire_r0_p[22], wire_r0_g[20], wire_r0_p[20]);
	gp_group1 gp_r1_21(wire_r1_g[21], wire_r1_p[21], wire_r0_g[21], wire_r0_p[21], wire_r0_g[19], wire_r0_p[19]);
	gp_group1 gp_r1_20(wire_r1_g[20], wire_r1_p[20], wire_r0_g[20], wire_r0_p[20], wire_r0_g[18], wire_r0_p[18]);
	gp_group1 gp_r1_19(wire_r1_g[19], wire_r1_p[19], wire_r0_g[19], wire_r0_p[19], wire_r0_g[17], wire_r0_p[17]);
	gp_group1 gp_r1_18(wire_r1_g[18], wire_r1_p[18], wire_r0_g[18], wire_r0_p[18], wire_r0_g[16], wire_r0_p[16]);
	gp_group1 gp_r1_17(wire_r1_g[17], wire_r1_p[17], wire_r0_g[17], wire_r0_p[17], wire_r0_g[15], wire_r0_p[15]);
	gp_group1 gp_r1_16(wire_r1_g[16], wire_r1_p[16], wire_r0_g[16], wire_r0_p[16], wire_r0_g[14], wire_r0_p[14]);
	//sample gp_r1_30(wire_r1_g[31], wire_r1_p[31], g_in_high, p_in_high, g_in_low, p_in_low);
	gp_group1 gp_r1_15(wire_r1_g[15], wire_r1_p[15], wire_r0_g[15], wire_r0_p[15], wire_r0_g[13], wire_r0_p[13]);
	gp_group1 gp_r1_14(wire_r1_g[14], wire_r1_p[14], wire_r0_g[14], wire_r0_p[14], wire_r0_g[12], wire_r0_p[12]);
	gp_group1 gp_r1_13(wire_r1_g[13], wire_r1_p[13], wire_r0_g[13], wire_r0_p[13], wire_r0_g[11], wire_r0_p[11]);
	gp_group1 gp_r1_12(wire_r1_g[12], wire_r1_p[12], wire_r0_g[12], wire_r0_p[12], wire_r0_g[10], wire_r0_p[10]);
	gp_group1 gp_r1_11(wire_r1_g[11], wire_r1_p[11], wire_r0_g[11], wire_r0_p[11], wire_r0_g[9], wire_r0_p[9]);
	gp_group1 gp_r1_10(wire_r1_g[10], wire_r1_p[10], wire_r0_g[10], wire_r0_p[10], wire_r0_g[8], wire_r0_p[8]);
	gp_group1 gp_r1_9(wire_r1_g[9], wire_r1_p[9], wire_r0_g[9], wire_r0_p[9], wire_r0_g[7], wire_r0_p[7]);
	gp_group1 gp_r1_8(wire_r1_g[8], wire_r1_p[8], wire_r0_g[8], wire_r0_p[8], wire_r0_g[6], wire_r0_p[6]);
	//sample gp_r1_30(wire_r1_g[31], wire_r1_p[31], g_in_high, p_in_high, g_in_low, p_in_low);
	gp_group1 gp_r1_7(wire_r1_g[7], wire_r1_p[7], wire_r0_g[7], wire_r0_p[7], wire_r0_g[5], wire_r0_p[5]);
	gp_group1 gp_r1_6(wire_r1_g[6], wire_r1_p[6], wire_r0_g[6], wire_r0_p[6], wire_r0_g[4], wire_r0_p[4]);
	gp_group1 gp_r1_5(wire_r1_g[5], wire_r1_p[5], wire_r0_g[5], wire_r0_p[5], wire_r0_g[3], wire_r0_p[3]);
	gp_group1 gp_r1_4(wire_r1_g[4], wire_r1_p[4], wire_r0_g[4], wire_r0_p[4], wire_r0_g[2], wire_r0_p[2]);
	gp_group1 gp_r1_3(wire_r1_g[3], wire_r1_p[3], wire_r0_g[3], wire_r0_p[3], wire_r0_g[1], wire_r0_p[1]);
	gp_group1 gp_r1_2(wire_r1_g[2], wire_r1_p[2], wire_r0_g[2], wire_r0_p[2], g[0], p[0]);
	
	assign c[2] = wire_r1_g[2];
	assign c[3] = wire_r1_g[3];

		//row 2
	//sample gp_r0_30(g_out, p_out, g_in_high, p_in_high, g_in_low, p_in_low);
	gp_group1 gp_r2_31(wire_r2_g[31], wire_r2_p[31], wire_r1_g[31], wire_r1_p[31], wire_r1_g[27], wire_r1_p[27]);
	gp_group1 gp_r2_30(wire_r2_g[30], wire_r2_p[30], wire_r1_g[30], wire_r1_p[30], wire_r1_g[26], wire_r1_p[26]);
	gp_group1 gp_r2_29(wire_r2_g[29], wire_r2_p[29], wire_r1_g[29], wire_r1_p[29], wire_r1_g[25], wire_r1_p[25]);
	gp_group1 gp_r2_28(wire_r2_g[28], wire_r2_p[28], wire_r1_g[28], wire_r1_p[28], wire_r1_g[24], wire_r1_p[24]);
	gp_group1 gp_r2_27(wire_r2_g[27], wire_r2_p[27], wire_r1_g[27], wire_r1_p[27], wire_r1_g[23], wire_r1_p[23]);
	gp_group1 gp_r2_26(wire_r2_g[26], wire_r2_p[26], wire_r1_g[26], wire_r1_p[26], wire_r1_g[22], wire_r1_p[22]);
	gp_group1 gp_r2_25(wire_r2_g[25], wire_r2_p[25], wire_r1_g[25], wire_r1_p[25], wire_r1_g[21], wire_r1_p[21]);
	gp_group1 gp_r2_24(wire_r2_g[24], wire_r2_p[24], wire_r1_g[24], wire_r1_p[24], wire_r1_g[20], wire_r1_p[20]);
	//sample gp_r2_30(wire_r2_g[31], wire_r2_p[31], g_in_high, p_in_high, g_in_low, p_in_low);
	gp_group1 gp_r2_23(wire_r2_g[23], wire_r2_p[23], wire_r1_g[23], wire_r1_p[23], wire_r1_g[19], wire_r1_p[19]);
	gp_group1 gp_r2_22(wire_r2_g[22], wire_r2_p[22], wire_r1_g[22], wire_r1_p[22], wire_r1_g[18], wire_r1_p[18]);
	gp_group1 gp_r2_21(wire_r2_g[21], wire_r2_p[21], wire_r1_g[21], wire_r1_p[21], wire_r1_g[17], wire_r1_p[17]);
	gp_group1 gp_r2_20(wire_r2_g[20], wire_r2_p[20], wire_r1_g[20], wire_r1_p[20], wire_r1_g[16], wire_r1_p[16]);
	gp_group1 gp_r2_19(wire_r2_g[19], wire_r2_p[19], wire_r1_g[19], wire_r1_p[19], wire_r1_g[15], wire_r1_p[15]);
	gp_group1 gp_r2_18(wire_r2_g[18], wire_r2_p[18], wire_r1_g[18], wire_r1_p[18], wire_r1_g[14], wire_r1_p[14]);
	gp_group1 gp_r2_17(wire_r2_g[17], wire_r2_p[17], wire_r1_g[17], wire_r1_p[17], wire_r1_g[13], wire_r1_p[13]);
	gp_group1 gp_r2_16(wire_r2_g[16], wire_r2_p[16], wire_r1_g[16], wire_r1_p[16], wire_r1_g[12], wire_r1_p[12]);
	//sample gp_r2_30(wire_r2_g[31], wire_r2_p[31], g_in_high, p_in_high, g_in_low, p_in_low);
	gp_group1 gp_r2_15(wire_r2_g[15], wire_r2_p[15], wire_r1_g[15], wire_r1_p[15], wire_r1_g[11], wire_r1_p[11]);
	gp_group1 gp_r2_14(wire_r2_g[14], wire_r2_p[14], wire_r1_g[14], wire_r1_p[14], wire_r1_g[10], wire_r1_p[10]);
	gp_group1 gp_r2_13(wire_r2_g[13], wire_r2_p[13], wire_r1_g[13], wire_r1_p[13], wire_r1_g[9], wire_r1_p[9]);
	gp_group1 gp_r2_12(wire_r2_g[12], wire_r2_p[12], wire_r1_g[12], wire_r1_p[12], wire_r1_g[8], wire_r1_p[8]);
	gp_group1 gp_r2_11(wire_r2_g[11], wire_r2_p[11], wire_r1_g[11], wire_r1_p[11], wire_r1_g[7], wire_r1_p[7]);
	gp_group1 gp_r2_10(wire_r2_g[10], wire_r2_p[10], wire_r1_g[10], wire_r1_p[10], wire_r1_g[6], wire_r1_p[6]);
	gp_group1 gp_r2_9(wire_r2_g[9], wire_r2_p[9], wire_r1_g[9], wire_r1_p[9], wire_r1_g[5], wire_r1_p[5]);
	gp_group1 gp_r2_8(wire_r2_g[8], wire_r2_p[8], wire_r1_g[8], wire_r1_p[8], wire_r1_g[4], wire_r1_p[4]);
	//sample gp_r2_30(wire_r2_g[31], wire_r2_p[31], g_in_high, p_in_high, g_in_low, p_in_low);
	gp_group1 gp_r2_7(wire_r2_g[7], wire_r2_p[7], wire_r1_g[7], wire_r1_p[7], wire_r1_g[3], wire_r1_p[3]);
	gp_group1 gp_r2_6(wire_r2_g[6], wire_r2_p[6], wire_r1_g[6], wire_r1_p[6], wire_r1_g[2], wire_r1_p[2]);
	gp_group1 gp_r2_5(wire_r2_g[5], wire_r2_p[5], wire_r1_g[5], wire_r1_p[5], wire_r0_g[1], wire_r0_p[1]);
	gp_group1 gp_r2_4(wire_r2_g[4], wire_r2_p[4], wire_r1_g[4], wire_r1_p[4], g[0], p[0]);

	assign c[4] = wire_r2_g[4];
	assign c[5] = wire_r2_g[5];
	assign c[6] = wire_r2_g[6];
	assign c[7] = wire_r2_g[7];
		//row 3
	//sample gp_r0_30(g_out, p_out, g_in_high, p_in_high, g_in_low, p_in_low);
	gp_group1 gp_r3_31(wire_r3_g[31], wire_r3_p[31], wire_r2_g[31], wire_r2_p[31], wire_r2_g[23], wire_r2_p[23]);
	gp_group1 gp_r3_30(wire_r3_g[30], wire_r3_p[30], wire_r2_g[30], wire_r2_p[30], wire_r2_g[22], wire_r2_p[22]);
	gp_group1 gp_r3_29(wire_r3_g[29], wire_r3_p[29], wire_r2_g[29], wire_r2_p[29], wire_r2_g[21], wire_r2_p[21]);
	gp_group1 gp_r3_28(wire_r3_g[28], wire_r3_p[28], wire_r2_g[28], wire_r2_p[28], wire_r2_g[20], wire_r2_p[20]);
	gp_group1 gp_r3_27(wire_r3_g[27], wire_r3_p[27], wire_r2_g[27], wire_r2_p[27], wire_r2_g[19], wire_r2_p[19]);
	gp_group1 gp_r3_26(wire_r3_g[26], wire_r3_p[26], wire_r2_g[26], wire_r2_p[26], wire_r2_g[18], wire_r2_p[18]);
	gp_group1 gp_r3_25(wire_r3_g[25], wire_r3_p[25], wire_r2_g[25], wire_r2_p[25], wire_r2_g[17], wire_r2_p[17]);
	gp_group1 gp_r3_24(wire_r3_g[24], wire_r3_p[24], wire_r2_g[24], wire_r2_p[24], wire_r2_g[16], wire_r2_p[16]);
	//sample gp_r3_30(wire_r3_g[31], wire_r3_p[31], g_in_high, p_in_high, g_in_low, p_in_low);
	gp_group1 gp_r3_23(wire_r3_g[23], wire_r3_p[23], wire_r2_g[23], wire_r2_p[23], wire_r2_g[15], wire_r2_p[15]);
	gp_group1 gp_r3_22(wire_r3_g[22], wire_r3_p[22], wire_r2_g[22], wire_r2_p[22], wire_r2_g[14], wire_r2_p[14]);
	gp_group1 gp_r3_21(wire_r3_g[21], wire_r3_p[21], wire_r2_g[21], wire_r2_p[21], wire_r2_g[13], wire_r2_p[13]);
	gp_group1 gp_r3_20(wire_r3_g[20], wire_r3_p[20], wire_r2_g[20], wire_r2_p[20], wire_r2_g[12], wire_r2_p[12]);
	gp_group1 gp_r3_19(wire_r3_g[19], wire_r3_p[19], wire_r2_g[19], wire_r2_p[19], wire_r2_g[11], wire_r2_p[11]);
	gp_group1 gp_r3_18(wire_r3_g[18], wire_r3_p[18], wire_r2_g[18], wire_r2_p[18], wire_r2_g[10], wire_r2_p[10]);
	gp_group1 gp_r3_17(wire_r3_g[17], wire_r3_p[17], wire_r2_g[17], wire_r2_p[17], wire_r2_g[9], wire_r2_p[9]);
	gp_group1 gp_r3_16(wire_r3_g[16], wire_r3_p[16], wire_r2_g[16], wire_r2_p[16], wire_r2_g[8], wire_r2_p[8]);
	//sample gp_r3_30(wire_r3_g[31], wire_r3_p[31], g_in_high, p_in_high, g_in_low, p_in_low);
	gp_group1 gp_r3_15(wire_r3_g[15], wire_r3_p[15], wire_r2_g[15], wire_r2_p[15], wire_r2_g[7], wire_r2_p[7]);
	gp_group1 gp_r3_14(wire_r3_g[14], wire_r3_p[14], wire_r2_g[14], wire_r2_p[14], wire_r2_g[6], wire_r2_p[6]);
	gp_group1 gp_r3_13(wire_r3_g[13], wire_r3_p[13], wire_r2_g[13], wire_r2_p[13], wire_r2_g[5], wire_r2_p[5]);
	gp_group1 gp_r3_12(wire_r3_g[12], wire_r3_p[12], wire_r2_g[12], wire_r2_p[12], wire_r2_g[4], wire_r2_p[4]);
	gp_group1 gp_r3_11(wire_r3_g[11], wire_r3_p[11], wire_r2_g[11], wire_r2_p[11], wire_r1_g[3], wire_r1_p[3]);
	gp_group1 gp_r3_10(wire_r3_g[10], wire_r3_p[10], wire_r2_g[10], wire_r2_p[10], wire_r1_g[2], wire_r1_p[2]);
	gp_group1 gp_r3_9(wire_r3_g[9], wire_r3_p[9], wire_r2_g[9], wire_r2_p[9], wire_r0_g[1], wire_r0_p[1]);
	gp_group1 gp_r3_8(wire_r3_g[8], wire_r3_p[8], wire_r2_g[8], wire_r2_p[8], g[0], p[0]);

	assign c[8] = wire_r3_g[8];
	assign c[9] = wire_r3_g[9];
	assign c[10] = wire_r3_g[10];
	assign c[11] = wire_r3_g[11];
	assign c[12] = wire_r3_g[12];
	assign c[13] = wire_r3_g[13];
	assign c[14] = wire_r3_g[14];
	assign c[15] = wire_r3_g[15];

		//row 4
	//sample gp_r0_30(g_out, p_out, g_in_high, p_in_high, g_in_low, p_in_low);		
	gp_group1 gp_r4_31(c[31], trash_propagate[31], wire_r3_g[31], wire_r3_p[31], wire_r3_g[15], wire_r3_p[15]);
	gp_group1 gp_r4_30(c[30], trash_propagate[30], wire_r3_g[30], wire_r3_p[30], wire_r3_g[14], wire_r3_p[14]);
	gp_group1 gp_r4_29(c[29], trash_propagate[29], wire_r3_g[29], wire_r3_p[29], wire_r3_g[13], wire_r3_p[13]);
	gp_group1 gp_r4_28(c[28], trash_propagate[28], wire_r3_g[28], wire_r3_p[28], wire_r3_g[12], wire_r3_p[12]);
	gp_group1 gp_r4_27(c[27], trash_propagate[27], wire_r3_g[27], wire_r3_p[27], wire_r3_g[11], wire_r3_p[11]);
	gp_group1 gp_r4_26(c[26], trash_propagate[26], wire_r3_g[26], wire_r3_p[26], wire_r3_g[10], wire_r3_p[10]);
	gp_group1 gp_r4_25(c[25], trash_propagate[25], wire_r3_g[25], wire_r3_p[25], wire_r3_g[9], wire_r3_p[9]);
	gp_group1 gp_r4_24(c[24], trash_propagate[24], wire_r3_g[24], wire_r3_p[24], wire_r3_g[8], wire_r3_p[8]);
	//sample gp_r4_30(g_out, p_out, g_in_high, p_in_high, g_in_low, p_in_low);
	gp_group1 gp_r4_23(c[23], trash_propagate[23], wire_r3_g[23], wire_r3_p[23], wire_r2_g[7], wire_r2_p[7]);
	gp_group1 gp_r4_22(c[22], trash_propagate[22], wire_r3_g[22], wire_r3_p[22], wire_r2_g[6], wire_r2_p[6]);
	gp_group1 gp_r4_21(c[21], trash_propagate[21], wire_r3_g[21], wire_r3_p[21], wire_r2_g[5], wire_r2_p[5]);
	gp_group1 gp_r4_20(c[20], trash_propagate[20], wire_r3_g[20], wire_r3_p[20], wire_r2_g[4], wire_r2_p[4]);
	gp_group1 gp_r4_19(c[19], trash_propagate[19], wire_r3_g[19], wire_r3_p[19], wire_r1_g[3], wire_r1_p[3]);
	gp_group1 gp_r4_18(c[18], trash_propagate[18], wire_r3_g[18], wire_r3_p[18], wire_r1_g[2], wire_r1_p[2]);
	gp_group1 gp_r4_17(c[17], trash_propagate[17], wire_r3_g[17], wire_r3_p[17], wire_r0_g[1], wire_r0_p[1]);
	gp_group1 gp_r4_16(c[16], trash_propagate[16], wire_r3_g[16], wire_r3_p[16], g[0], p[0]);


endmodule



