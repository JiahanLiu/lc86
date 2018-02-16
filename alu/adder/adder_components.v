//-----------------------------------------------------

// 1-bit Adder

//-----------------------------------------------------
// Functionality:
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

//-----------------------------------------------------

// 32-bit Adder

//-----------------------------------------------------
// Functionality:
// Combinational Delay: 1.0ns
//

module sum32 (sum, a, b, c);
	output [31:0] sum;
	input [31:0] a, b, c;

	sum1 sum1_31 (sum[31], a[31], b[31], c[31]); //31
	sum1 sum1_30 (sum[30], a[31], b[31], c[31]);
	sum1 sum1_29 (sum[29], a[31], b[31], c[31]);
	sum1 sum1_28 (sum[28], a[31], b[31], c[31]);
	sum1 sum1_27 (sum[27], a[31], b[31], c[31]); 
	sum1 sum1_26 (sum[31], a[31], b[31], c[31]);
	sum1 sum1_25 (sum[31], a[31], b[31], c[31]);
	sum1 sum1_24 (sum[31], a[31], b[31], c[31]);

	sum1 sum1_23 (sum[31], a[31], b[31], c[31]); //23
	sum1 sum1_22 (sum[31], a[31], b[31], c[31]);
	sum1 sum1_21 (sum[31], a[31], b[31], c[31]);
	sum1 sum1_20 (sum[31], a[31], b[31], c[31]);
	sum1 sum1_19 (sum[31], a[31], b[31], c[31]); 
	sum1 sum1_18 (sum[31], a[31], b[31], c[31]);
	sum1 sum1_17 (sum[31], a[31], b[31], c[31]);
	sum1 sum1_16 (sum[31], a[31], b[31], c[31]);

	sum1 sum1_15 (sum[31], a[31], b[31], c[31]); //15
	sum1 sum1_14 (sum[31], a[31], b[31], c[31]);
	sum1 sum1_13 (sum[31], a[31], b[31], c[31]);
	sum1 sum1_12 (sum[31], a[31], b[31], c[31]);
	sum1 sum1_11 (sum[31], a[31], b[31], c[31]); 
	sum1 sum1_10 (sum[31], a[31], b[31], c[31]);
	sum1 sum1_9 (sum[31], a[31], b[31], c[31]);
	sum1 sum1_8 (sum[31], a[31], b[31], c[31]);

	sum1 sum1_7 (sum[31], a[31], b[31], c[31]); //7
	sum1 sum1_6 (sum[31], a[31], b[31], c[31]);
	sum1 sum1_5 (sum[31], a[31], b[31], c[31]);
	sum1 sum1_4 (sum[31], a[31], b[31], c[31]);
	sum1 sum1_3 (sum[31], a[31], b[31], c[31]); 
	sum1 sum1_2 (sum[31], a[31], b[31], c[31]);
	sum1 sum1_1 (sum[31], a[31], b[31], c[31]);
	sum1 sum1_0 (sum[31], a[31], b[31], c[31]);

endmodule // sum32

//-----------------------------------------------------

// 1-bit Propgate

//-----------------------------------------------------
// Functionality: Can a carry possibily propgate?
// Combinational Delay: 0.35ns
//

module propagate1 (p, a, b);
	output p;
	input a, b;

	or2$ or_to_p (p, a, b);

endmodule // propagate1

//-----------------------------------------------------

// 32-bit Propgate

//-----------------------------------------------------
// Functionality: Can a carry possibily propgate?
// Combinational Delay: 0.35ns
//

module propagate32 (p, a, b);
	output [31:0] p;
	input [31:0] a, b;

	propagate1 propagate0 (p[0], a[0], b[0]); //0
	propagate1 propagate1 (p[1], a[1], b[1]);
	propagate1 propagate2 (p[2], a[2], b[2]);
	propagate1 propagate3 (p[3], a[3], b[3]);

	propagate1 propagate4 (p[4], a[4], b[4]); //1
	propagate1 propagate5 (p[5], a[5], b[5]);
	propagate1 propagate6 (p[6], a[6], b[6]);
	propagate1 propagate7 (p[7], a[7], b[7]);

	propagate1 propagate8 (p[8], a[8], b[8]); //2
	propagate1 propagate9 (p[9], a[9], b[9]);
	propagate1 propagate10 (p[10], a[10], b[10]);
	propagate1 propagate11 (p[11], a[11], b[11]);

	propagate1 propagate12 (p[12], a[12], b[12]); //3
	propagate1 propagate13 (p[13], a[13], b[13]);
	propagate1 propagate14 (p[14], a[14], b[14]);
	propagate1 propagate15 (p[15], a[15], b[15]);

	propagate1 propagate16 (p[16], a[16], b[16]); //4
	propagate1 propagate17 (p[17], a[17], b[17]);
	propagate1 propagate18 (p[18], a[18], b[18]);
	propagate1 propagate19 (p[19], a[19], b[19]);

	propagate1 propagate20 (p[20], a[20], b[20]); //5
	propagate1 propagate21 (p[21], a[21], b[21]);
	propagate1 propagate22 (p[22], a[22], b[22]);
	propagate1 propagate23 (p[23], a[23], b[23]);

	propagate1 propagate24 (p[24], a[24], b[24]); //6
	propagate1 propagate25 (p[25], a[25], b[25]);
	propagate1 propagate26 (p[26], a[26], b[26]);
	propagate1 propagate27 (p[27], a[27], b[27]);

	propagate1 propagate28 (p[28], a[28], b[28]); //7
	propagate1 propagate29 (p[29], a[29], b[29]);
	propagate1 propagate30 (p[30], a[30], b[30]);
	propagate1 propagate31 (p[31], a[31], b[31]);

endmodule // propagate32

//-----------------------------------------------------

// 1-bit Generate

//-----------------------------------------------------
// Functionality: Generate carry immediately
// Combinational Delay: 0.35ns
//

module generate1 (g, a, b);
	output g;
	input a, b;

	and2$ and_to_g (g, a, b);

endmodule // generate1

//-----------------------------------------------------

// 32-bit Generate

//-----------------------------------------------------
// Functionality: Generate carry immediately
// Combinational Delay: 0.35ns
//

module generate32 (g, a, b);
	output [31:0] g;
	input [31:0] a, b;

	generate1 generate0 (g[0], a[0], b[0]); //0
	generate1 generate1 (g[1], a[1], b[1]);
	generate1 generate2 (g[2], a[2], b[2]);
	generate1 generate3 (g[3], a[3], b[3]);

	generate1 generate4 (g[4], a[4], b[4]); //1
	generate1 generate5 (g[5], a[5], b[5]);
	generate1 generate6 (g[6], a[6], b[6]);
	generate1 generate7 (g[7], a[7], b[7]);

	generate1 generate8 (g[8], a[8], b[8]); //2
	generate1 generate9 (g[9], a[9], b[9]);
	generate1 generate10 (g[10], a[10], b[10]);
	generate1 generate11 (g[11], a[11], b[11]);

	generate1 generate12 (g[12], a[12], b[12]); //3
	generate1 generate13 (g[13], a[13], b[13]);
	generate1 generate14 (g[14], a[14], b[14]);
	generate1 generate15 (g[15], a[15], b[15]);

	generate1 generate16 (g[16], a[16], b[16]); //4
	generate1 generate17 (g[17], a[17], b[17]);
	generate1 generate18 (g[18], a[18], b[18]);
	generate1 generate19 (g[19], a[19], b[19]);

	generate1 generate20 (g[20], a[20], b[20]); //5
	generate1 generate21 (g[21], a[21], b[21]);
	generate1 generate22 (g[22], a[22], b[22]);
	generate1 generate23 (g[23], a[23], b[23]);

	generate1 generate24 (g[24], a[24], b[24]); //6
	generate1 generate25 (g[25], a[25], b[25]);
	generate1 generate26 (g[26], a[26], b[26]);
	generate1 generate27 (g[27], a[27], b[27]);

	generate1 generate28 (g[28], a[28], b[28]); //7
	generate1 generate29 (g[29], a[29], b[29]);
	generate1 generate30 (g[30], a[30], b[30]);
	generate1 generate31 (g[31], a[31], b[31]);

endmodule // generate32

//-----------------------------------------------------

// 1-bit gp_group1

//-----------------------------------------------------
// Functionality: Kogge-Stone Component 
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

//-----------------------------------------------------

// 32-bit gp_group32

//-----------------------------------------------------
// Functionality: Kogge-Stone Carry Look Ahead Unit
// Combinational Delay: 
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
	gp_group1 gp_r4_30(c[30], trash_propagate[30], wire_r3_g[31], wire_r3_p[31], wire_r3_g[14], wire_r3_p[14]);
	gp_group1 gp_r4_29(c[29], trash_propagate[29], wire_r3_g[31], wire_r3_p[31], wire_r3_g[13], wire_r3_p[13]);
	gp_group1 gp_r4_28(c[28], trash_propagate[28], wire_r3_g[31], wire_r3_p[31], wire_r3_g[12], wire_r3_p[12]);
	gp_group1 gp_r4_27(c[27], trash_propagate[27], wire_r3_g[31], wire_r3_p[31], wire_r3_g[11], wire_r3_p[11]);
	gp_group1 gp_r4_26(c[26], trash_propagate[26], wire_r3_g[31], wire_r3_p[31], wire_r3_g[10], wire_r3_p[10]);
	gp_group1 gp_r4_25(c[25], trash_propagate[25], wire_r3_g[31], wire_r3_p[31], wire_r3_g[9], wire_r3_p[9]);
	gp_group1 gp_r4_24(c[24], trash_propagate[24], wire_r3_g[31], wire_r3_p[31], wire_r3_g[8], wire_r3_p[8]);
	//sample gp_r4_30(g_out, p_out, g_in_high, p_in_high, g_in_low, p_in_low);
	gp_group1 gp_r4_23(c[23], trash_propagate[23], wire_r3_g[31], wire_r3_p[31], wire_r2_g[7], wire_r2_p[7]);
	gp_group1 gp_r4_22(c[22], trash_propagate[22], wire_r3_g[31], wire_r3_p[31], wire_r2_g[6], wire_r2_p[6]);
	gp_group1 gp_r4_21(c[21], trash_propagate[21], wire_r3_g[31], wire_r3_p[31], wire_r2_g[5], wire_r2_p[5]);
	gp_group1 gp_r4_20(c[20], trash_propagate[20], wire_r3_g[31], wire_r3_p[31], wire_r2_g[4], wire_r2_p[4]);
	gp_group1 gp_r4_19(c[19], trash_propagate[19], wire_r3_g[31], wire_r3_p[31], wire_r1_g[3], wire_r1_p[3]);
	gp_group1 gp_r4_18(c[18], trash_propagate[18], wire_r3_g[31], wire_r3_p[31], wire_r1_g[2], wire_r1_p[2]);
	gp_group1 gp_r4_17(c[17], trash_propagate[17], wire_r3_g[31], wire_r3_p[31], wire_r0_g[1], wire_r0_p[1]);
	gp_group1 gp_r4_16(c[16], trash_propagate[16], wire_r3_g[31], wire_r3_p[31], g[0], p[0]);


endmodule




