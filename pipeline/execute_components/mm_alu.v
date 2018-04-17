//-------------------------------------------------------------------------------------
//
// 									  ALU64
//
//-------------------------------------------------------------------------------------
// Functionality: PADDW
//
// Combinational Delay: 
//
module alu64(
	output [63:0] alu64_results,
	input [63:0] MM_A,
	input [63:0] MM_B,
	input [31:0] imm, 
	input [2:0] operation_select
	);
	
	wire [63:0]	PADDW_result, PADDD_result, PADDSW_result, PSHUFW_result, Pass_result, Swap_result; 

	PADDW u_PADDW(PADDW_result, MM_A, MM_B);
	PADDD u_PADDD(PADDD_result, MM_A, MM_B);
	PADDSW u_PADDSW(PADDSW_result, MM_A, MM_B);
	PSHUFW u_PSHUFW(PSHUFW_result, MM_B, imm[7:0]);
	assign Pass_result = MM_A; 
	assign Swap_result = MM_B;

	mux64_8way result_mux(alu64_results, PADDW_result, PADDD_result, PADDSW_result, PSHUFW_result, Pass_result, Swap_result, , ,operation_select);	
	
endmodule // alu64
//-------------------------------------------------------------------------------------
//
// 									  PADDW
//
//-------------------------------------------------------------------------------------
// Functionality: PADDW
//
// Combinational Delay: 
//
module PADDW(
	output [63:0] alu64_results,
	input [63:0] a,
	input [63:0] b
	);
	
	wire [31:0] result3, result2, result1, result0;
	wire [31:0] a3, a2, a1, a0, b3, b2, b1, b0;
	assign a3[31:16] = 16'h0000;
	assign a3[15:0] = a[63:48];
	assign a2[31:16] = 16'h0000;
	assign a2[15:0] = a[47:32];
	assign a1[31:16] = 16'h0000;
	assign a1[15:0] = a[31:16];
	assign a0[31:16] = 16'h0000;
	assign a0[15:0] = a[15:0];

    assign b3[31:16] = 16'h0000;
	assign b3[15:0] = b[63:48];
	assign b2[31:16] = 16'h0000;
	assign b2[15:0] = b[47:32];
	assign b1[31:16] = 16'h0000;
	assign b1[15:0] = b[31:16];
	assign b0[31:16] = 16'h0000;
	assign b0[15:0] = b[15:0];


	adder32 adder_3(result3, , a3, b3);
	adder32 adder_2(result2, , a2, b2);
	adder32 adder_1(result1, , a1, b1);
	adder32 adder_0(result0, , a0, b0);

	assign alu64_results[63:48] = result3[15:0];
	assign alu64_results[47:32] = result2[15:0];
	assign alu64_results[31:16] = result1[15:0];
	assign alu64_results[15:0] = result0[15:0];  		

endmodule // PADDW
//-------------------------------------------------------------------------------------
//
// 									   PADDD
//
//-------------------------------------------------------------------------------------
// Functionality: PADDD
//
// Combinational Delay: 
//
module PADDD(
	output [63:0] alu64_results,
	input [63:0] a,
	input [63:0] b
	);

	adder32 adder_high(alu64_results[63:32], ,a[63:32], b[63:32]);
	adder32 adder_low(alu64_results[31:0], ,a[31:0], b[31:0]);

endmodule // PADDD

//-------------------------------------------------------------------------------------
//
// 									   PADDSW
//
//-------------------------------------------------------------------------------------
// Functionality: PADDSW
//
// Combinational Delay: 
//
module PADDSW(
	output [63:0] alu64_results,
	input [63:0] a,
	input [63:0] b
	);

	wire [63:0] intermediate_result;

	adder32 adder_high(intermediate_result[63:32], ,a[63:32], b[63:32]);
	adder32 adder_low(intermediate_result[31:0], ,a[31:0], b[31:0]);

	wire a_63_not, a_31_not, b_63_not, b_31_not, result_63_not, result_31_not; 

	inv1$ u_not_a_63(a_63_not, a[63]);
	inv1$ u_not_a_31(a_31_not, a[31]);
	inv1$ u_not_b_63(b_63_not, b[63]);
	inv1$ u_not_b_31(b_31_not, b[31]);
	inv1$ u_not_result_63(result_63_not, intermediate_result[63]);
	inv1$ u_not_result_31(result_31_not, intermediate_result[31]);

	wire positive_sat_1, positive_sat_0, negative_sat_1, negative_sat_0;

	and3$ u_pos_sat_1(positive_sat_1, a_63_not, b_63_not, intermediate_result[63]);
	and3$ u_pos_sat_0(positive_sat_0, a_31_not, b_31_not, intermediate_result[31]);
	and3$ u_neg_sat_1(negative_sat_1, a[63], b[63], result_63_not);
	and3$ u_neg_sat_0(negative_sat_0, a[31], b[31], result_31_not);

	wire [63:0] post_pos_sat;

	mux32_2way u_mux_pos_sat1(post_pos_sat[63:32], intermediate_result[63:32], 32'h7FFF, positive_sat_1);
	mux32_2way u_mux_neg_sat1(alu64_results[63:32], post_pos_sat[63:32], 32'h8000, negative_sat_1);
	mux32_2way u_mux_pos_sat0(post_pos_sat[31:0], intermediate_result[31:0], 32'h7FFF, positive_sat_0);
	mux32_2way u_mux_neg_sat0(alu64_results[31:0], post_pos_sat[31:0], 32'h8000, negative_sat_0);

endmodule // PADDSW
//-------------------------------------------------------------------------------------
//
// 									   PSHUFW
//
//-------------------------------------------------------------------------------------
// Functionality: PSHUFW
//
// Combinational Delay: 
//
module PSHUFW(
	output [63:0] alu64_results,
	input [63:0] b,
	input [7:0] c 
	);

	mux16_4way u_mux3(alu64_results[63:48], b[15:0], b[31:16], b[47:32], b[63:48], c[7:6]);
	mux16_4way u_mux2(alu64_results[47:32], b[15:0], b[31:16], b[47:32], b[63:48], c[5:4]);
	mux16_4way u_mux1(alu64_results[31:16], b[15:0], b[31:16], b[47:32], b[63:48], c[3:2]);
	mux16_4way u_mux0(alu64_results[15:0], b[15:0], b[31:16], b[47:32], b[63:48], c[1:0]);
	
endmodule // PSHUFW
