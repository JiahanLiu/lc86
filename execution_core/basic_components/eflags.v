
//-------------------------------------------------------------------------------------
//
// 					 		Reference: Intel Vol1, pg 60
//
//-------------------------------------------------------------------------------------
//-------------------------------------------------------------------------------------
// eflags.v
// --------------------
// EE382N, Spring 2018
// Apruv Narkhede, Nelson Wu, Steven Flolid, Jiahan Liu
//
// OF_logic                         - Overflow Flag                  
// PF_logic                         - Parity Flag                    
// ZF_logic                         - Zero Flag                      
// ZF_logic_daa                     - Zero Flag for DAA instruction  
// assign_flags                     - Assigns individual flag bits to 32 bit flag register
//
//-------------------------------------------------------------------------------------

//-------------------------------------------------------------------------------------
//
// 					 				OF_Logic
//
//-------------------------------------------------------------------------------------
// Functionality: Overflow Flag
//
// Combinational Delay: 
//
module OF_logic (
	output OF,
	input adder_result_high_bit, // Clock Enable
	input a_high_bit,
	input b_high_bit
	);

	wire xor_result_a, xnor_a_b; 

	xor2$ u_xor_of(xor_result_a, adder_result_high_bit, a_high_bit);
	xnor2$ u_xnor_of(xnor_a_b, a_high_bit, b_high_bit);
	and2$ u_xand_of (OF, xor_result_a, xnor_a_b); 	

endmodule

//-------------------------------------------------------------------------------------
//
// 					 				PF_Logic
//
//-------------------------------------------------------------------------------------
// Functionality: Parity Flag
//
// Combinational Delay: 
//
module PF_logic (
	output PF,    // Clock
	input [7:0] adder_result // Clock Enable
	);

	//PF
	wire PF_7_6, PF_5_4, PF_3_2, PF_1_0;
	wire PF_7_4, PF_3_0;

	xnor2$ u_xor2_pf_7_6 (PF_7_6, adder_result[7], adder_result[6]);
	xnor2$ u_xor2_pf_5_4 (PF_5_4, adder_result[5], adder_result[4]);
	xnor2$ u_xor2_pf_3_2 (PF_3_2, adder_result[3], adder_result[2]);
	xnor2$ u_xor2_pf_1_0 (PF_1_0, adder_result[1], adder_result[0]);

	xnor2$ u_xor2_pf_7_4 (PF_7_4, PF_7_6, PF_5_4);
	xnor2$ u_xor2_pf_3_0 (PF_3_0, PF_3_2, PF_1_0);

	xnor2$ u_xor2_pf_7_0 (PF, PF_7_4, PF_3_0);	

endmodule

//-------------------------------------------------------------------------------------
//
// 					 				ZF_Logic
//
//-------------------------------------------------------------------------------------
// Functionality: Zero Flag
// 
// Notes: Use a different one for DAA
// 
// Combinational Delay: 
//
module ZF_logic (
	output ZF,    
	input [31:0] adder_result
	);

	//ZF
	wire ZF_31_28, ZF_27_24, ZF_23_20, ZF_19_16, ZF_15_12, ZF_11_8, ZF_7_4, ZF_3_0;
	wire ZF_31_16, ZF_15_0, ZF_N; 
	//layer 1
	or4$ u_or_zf_31_28(ZF_31_28, adder_result[31], adder_result[30], adder_result[29], adder_result[28]);
	or4$ u_or_zf_27_24(ZF_27_24, adder_result[27], adder_result[26], adder_result[25], adder_result[24]);
	or4$ u_or_zf_23_20(ZF_23_20, adder_result[23], adder_result[22], adder_result[21], adder_result[20]);
	or4$ u_or_zf_19_16(ZF_19_16, adder_result[19], adder_result[18], adder_result[17], adder_result[16]);
	
	or4$ u_or_zf_15_12(ZF_15_12, adder_result[15], adder_result[14], adder_result[13], adder_result[12]);
	or4$ u_or_zf_11_8(ZF_11_8, adder_result[11], adder_result[10], adder_result[9], adder_result[8]);
	or4$ u_or_zf_7_4(ZF_7_4, adder_result[7], adder_result[6], adder_result[5], adder_result[4]);
	or4$ u_or_zf_3_0(ZF_3_0, adder_result[3], adder_result[2], adder_result[1], adder_result[0]);
	//layer 2
	or4$ u_or_zf_31_16(ZF_31_16, ZF_31_28, ZF_27_24, ZF_23_20, ZF_19_16);
	or4$ u_or_zf_15_0(ZF_15_0, ZF_15_12, ZF_11_8, ZF_7_4, ZF_3_0);
	//layer 3
	or2$ u_or_zf_31_0(ZF_N, ZF_31_16, ZF_15_0);
    inv1$ inv1 (ZF, ZF_N);

endmodule

//-------------------------------------------------------------------------------------
//
// 					 			ZF_Logic for DAA
//
//-------------------------------------------------------------------------------------
// Functionality: Zero Flag for DAA instruction
// 
// Notes: Use a different one for DAA
// 
// Combinational Delay: 
//
module ZF_logic_daa (
	output ZF,    
	input [7:0] adder_result
	);

	//ZF
	wire ZF_7_4, ZF_3_0; 

	or4$ u_or_zf_7_4(ZF_7_4, adder_result[7], adder_result[6], adder_result[5], adder_result[4]);
	or4$ u_or_zf_3_0(ZF_3_0, adder_result[3], adder_result[2], adder_result[1], adder_result[0]);

	or2$ u_or_zf_31_0(ZF, ZF_7_4, ZF_3_0);

endmodule

//-------------------------------------------------------------------------------------
//
// 					 		Assign 1 bit Flags to 32 Bit Register
//
//-------------------------------------------------------------------------------------
// Functionality: Assigns individual flag bits to 32 bit flag register
// 
// Combinational Delay: 
//
module assign_flags (
	output [31:0] flags,
	input OF,
	input DF,
	input SF,
	input ZF,
	input AF,
	input PF,
	input CF
	);

	//assign to flag output
	assign flags[31:12] = 20'h00000;

	assign flags[11] = OF; 
	assign flags[10] = DF; 

	assign flags[9:8] = 2'b00;

	assign flags[7] = SF; 
	assign flags[6] = ZF; 

	assign flags[5] = 1'b0; 
	assign flags[4] = AF; 
	assign flags[3] = 1'b0; 
	assign flags[2] = PF; 
	assign flags[1] = 1'b0; 
	assign flags[0] = CF; 

endmodule
