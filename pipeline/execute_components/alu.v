//-------------------------------------------------------------------------------------
// alu.v
// --------------------
// EE382N, Spring 2018
// Apruv Narkhede, Nelson Wu, Steven Flolid, Jiahan Liu
//
// alu32                            - 32-bit ALU                     
// alu_adder                        - adds a and b, produces flags   
// alu_or                           - 32-bitwise OR, produces flags  
// alu_not                          - 32-bitwise NOT, produces flags 
// alu_daa                          - decimal adjust, produces flags 
// daa_single_digit                 - decimal adjust for 1-digit (4 bits)
// daa_double_digit                 - decimal adjust for 2-digit (8 bits), produces flags
// alu_and                          - 32-bitwise AND, produces flags 
// alu_cld                          - produces a 32-bit flag with DF = 0
// alu_cmp                          - does a compare by subtracting, produces flags
// alu_std                          - produces a 32-bit flag with DF = 1
//
//-------------------------------------------------------------------------------------
//-------------------------------------------------------------------------------------
//
// 									  ALU32
//
//-------------------------------------------------------------------------------------
// Functionality: 32-bit ALU
//
// Operations 0 = ADD | 1 == OR | 2 = NOT | 3 = DAA | 4 = AND
//            | 5 = CLD | 6 = CMP | 7 = STD
//
// Combinational Delay: 4.2ns
//
module alu32 (alu_out, flags, a, b, op);
	output [31:0] alu_out;
	output [31:0] flags;
	input [31:0] a, b;
	input [2:0] op;

	wire [31:0] adder_result, or_result, not_result, daa_result, and_result, cld_result, cmp_result, std_result;
	wire [31:0] adder_flags, or_flags, not_flags, daa_flags, and_flags, cld_flags, cmp_flags, std_flags;

	wire [31:0] bufferedA [3:0];
	wire [31:0] bufferedB[3:0];

	buffer32_16way u_bufferA(bufferedA[0], bufferedA[1], bufferedA[2], bufferedA[3], a);
	buffer32_16way u_bufferB(bufferedB[0], bufferedB[1], bufferedB[2], bufferedB[3], b);

	alu_adder u_alu_adder (adder_result, adder_flags, bufferedA[0], bufferedB[0]);
	alu_or u_alu_or (or_result, or_flags, bufferedA[0], bufferedB[0]);
	alu_not u_alu_not (not_result, not_flags, bufferedA[0]);
	alu_daa u_alu_daa (daa_result, daa_flags, bufferedA[0]);
	alu_and u_alu_and (and_result, and_flags, bufferedA[1], bufferedB[1]);
	alu_cld u_alu_cld (cld_result, cld_flags);
	alu_cmp u_alu_cmp (cmp_result, cmp_flags, bufferedB[1], bufferedA[1]); //inverted because of how Nelson gives me the data
	alu_std u_alu_std (std_result, std_flags);

	mux32_8way out_selection(alu_out, adder_result, or_result, not_result, daa_result, and_result, cld_result, cmp_result, std_result, op[2:0]);
	mux32_8way flag_selection(flags, adder_flags, or_flags, not_flags, daa_flags, and_flags, cld_flags, cmp_flags, std_flags, op[2:0]);

endmodule // alu
//-------------------------------------------------------------------------------------
//
// 									  ALU_Adder32
//
//-------------------------------------------------------------------------------------
// Functionality: adds a and b, produces flags
//
// Combinational Delay: 4.2ns
//
module alu_adder (adder_result, flags, a, b);
	output [31:0] adder_result;
	output [31:0] flags;
	input [31:0] a, b;

	wire [31:0] adder_carry; 
	adder32 u_adder32(adder_result, adder_carry, a, b);  

	wire OF, DF, SF, ZF, AF, PF, CF; 

	OF_logic u_OF_logic(OF, adder_result[31], a[31], b[31]);
	assign DF = 0;
	assign SF = adder_result[31];
	ZF_logic u_ZF_logic(ZF, adder_result[31:0]);
	assign AF = adder_carry[3];
	PF_logic u_PF_logic(PF, adder_result[7:0]);
	assign CF = adder_carry[31];

	assign_flags u_assign_flags(flags[31:0], OF, DF, SF, ZF, AF, PF, CF);	

endmodule

//-------------------------------------------------------------------------------------
//
// 									  ALU_OR32
//
//-------------------------------------------------------------------------------------
// Functionality: 32-bitwise OR, produces flags
//
// Combinational Delay: 4.2ns
//
module alu_or (
	output [31:0] or_result,
	output [31:0] flags,
	input [31:0] a, b
	);

	or32_2way u_or32_2way(or_result, a, b);

	wire OF, DF, SF, ZF, AF, PF, CF;  

	assign OF = 0;
	assign DF = 0;
	assign SF = or_result[31];
	ZF_logic u_ZF_logic(ZF, or_result[31:0]);
	assign AF = 0;
	PF_logic u_PF_logic(PF, or_result[7:0]);
	assign CF = 0;

	assign_flags u_assign_flags(flags[31:0], OF, DF, SF, ZF, AF, PF, CF);	
endmodule

//-------------------------------------------------------------------------------------
//
// 									  ALU_NOT32
//
//-------------------------------------------------------------------------------------
// Functionality: 32-bitwise NOT, produces flags
//
// Combinational Delay: 4.2ns
//
module alu_not (
	output [31:0] not_result,
	output [31:0] flags,
	input [31:0] a
	);

	not32_1way u_not32_1way(not_result, a);

	wire OF, DF, SF, ZF, AF, PF, CF;  

	assign OF = 0;
	assign DF = 0;
	assign SF = 0;
	assign ZF = 0;
	assign AF = 0;
	assign PF = 0;
	assign CF = 0;

	assign_flags u_assign_flags(flags[31:0], OF, DF, SF, ZF, AF, PF, CF);	
endmodule

//-------------------------------------------------------------------------------------
//
// 									  ALU_DAA32
//
//-------------------------------------------------------------------------------------
// Functionality: decimal adjust, produces flags
//
// Combinational Delay: 4.2ns
//
module alu_daa (
	output [31:0] daa_result,
	output [31:0] flags,
	input [31:0] a
	);

	wire [1:0] daa_carry_out;
	daa_double_digit u_daa_double_digit(daa_result[7:0], daa_carry_out, a[7:0]);

	wire OF, DF, SF, ZF, AF, PF, CF;  

	assign OF = 0;
	assign DF = 0;
	assign SF = 0; //bcd is unsigned, vol1, page 80
	ZF_logic_daa u_ZF_logic_daa(ZF, daa_result[7:0]);
	or2$ u_AF(AF, daa_carry_out[0], daa_carry_out[1]); //different for DAA
	PF_logic u_PF_logic(PF, daa_result[7:0]);
	or2$ u_CF(CF, daa_carry_out[0], daa_carry_out[1]); //different for DAA

	assign_flags u_assign_flags(flags[31:0], OF, DF, SF, ZF, AF, PF, CF);	
endmodule

//-------------------------------------------------------------------------------------
//
// 									 DAA for Single Digit
//
//-------------------------------------------------------------------------------------
// Functionality: decimal adjust for 1-digit (4 bits)
//
// Combinational Delay: 4.2ns
//
module daa_single_digit (
	output [3:0] digit_out, 
	output carry_out, 
	input [3:0] a,
	input carry_in
	);

	wire [3:0] a_not;
	wire carry_in_not;

	not4_1way not_a(a_not, a);
	inv1$ not_carry_in(carry_in_not, carry_in);

	wire and3_comp1, and3_comp2, and3_comp3;
	wire and2_comp1, and2_comp2, and2_comp3, and2_comp4, and2_comp5;
	wire and1_comp1, and1_comp2, and1_comp3, and1_comp4, and1_comp5, and1_comp6;
	wire and0_comp1, and0_comp2;
	wire andCarry_comp1, andCarry_comp2, andCarry_comp3;
	
	//or_comp1
	and1_5way u_and3_comp1(and3_comp1, a_not[3], a[2], a[1], a[0], carry_in);
	and4$ u_and3_comp2(and3_comp2, a[3], a_not[2], a_not[1], a_not[0]);
	and4$ u_and3_comp3(and3_comp3, a[3], a_not[2], a_not[1], carry_in_not);
	//or_comp2
	and1_5way u_and2_comp1(and2_comp1, a_not[3], a_not[2], a[1], a[0], carry_in);
	and3$ u_and2_comp2(and2_comp2, a[3], a[2], a[1]);
	and3$ u_and2_comp3(and2_comp3, a_not[3], a[2], a_not[0]);
	and3$ u_and2_comp4(and2_comp4, a_not[3], a[2], carry_in_not);
	and4$ u_and2_comp5(and2_comp5, a[2], a_not[1], a[0], carry_in);
	//or_comp3
	and4$ u_and1_comp1(and1_comp1, a_not[3], a_not[1], a[0], carry_in);
	and3$ u_and1_comp2(and1_comp2, a_not[3], a[1], a_not[0]);
	and3$ u_and1_comp3(and1_comp3, a_not[3], a[1], carry_in_not);
	and4$ u_and1_comp4(and1_comp4, a[3], a[1], a[0], carry_in);
	and4$ u_and1_comp5(and1_comp5, a[3], a[2], a_not[1], a_not[0]);
	and4$ u_and1_comp6(and1_comp6, a[3], a[2], a_not[1], carry_in_not);
	//or_comp4
	and2$ u_and0_comp1(and0_comp1, a_not[0], carry_in);
	and2$ u_and0_comp2(and0_comp2, a[0], carry_in_not);
	//or_comp5
	and3$ u_andCarry_comp1(andCarry_comp1, a[3], a[0], carry_in);
	and2$ u_andCarry_comp2(andCarry_comp2, a[3], a[1]);
	and2$ u_andCarry_comp3(andCarry_comp3, a[3], a[2]);

	or3$ u_or_final_1(digit_out[3], and3_comp1, and3_comp2, and3_comp3);
	or1_5way u_or_final_2(digit_out[2], and2_comp1, and2_comp2, and2_comp3, and2_comp4, and2_comp5);
	or1_6way u_or_final_3(digit_out[1], and1_comp1, and1_comp2, and1_comp3, and1_comp4, and1_comp5, and1_comp6);
	or2$ u_or_final_4(digit_out[0], and0_comp1, and0_comp2);
	or3$ u_or_final_5(carry_out, andCarry_comp1, andCarry_comp2, andCarry_comp3);

endmodule

//-------------------------------------------------------------------------------------
//
// 									 DAA for Double Digit
//
//-------------------------------------------------------------------------------------
// Functionality: decimal adjust for 2-digit (8 bits), produces flags
//
// Combinational Delay: 4.2ns
//
module daa_double_digit (
	output [7:0] digits_out,
	output [1:0] carry_out, 
	input [7:0] digits_in
	);

	wire intermediate_carry;

	daa_single_digit u_digit_low(digits_out[3:0], intermediate_carry, digits_in[3:0], 1'b0);
	daa_single_digit u_digit_high(digits_out[7:4], carry_out[1], digits_in[7:4], intermediate_carry);
	assign carry_out[0] = intermediate_carry;


endmodule

//-------------------------------------------------------------------------------------
//
// 									  ALU_AND32
//
//-------------------------------------------------------------------------------------
// Functionality: 32-bitwise AND, produces flags
//
// Combinational Delay: 4.2ns
//
module alu_and (
	output [31:0] and_result,
	output [31:0] flags,
	input [31:0] a, b
	);

	and32_2way and32_2way (and_result, a, b);

	wire OF, DF, SF, ZF, AF, PF, CF;  

	assign OF = 0;
	assign DF = 0;
	assign SF = and_result[31];
	ZF_logic u_ZF_logic(ZF, and_result[31:0]);
	assign AF = 0;
	PF_logic u_PF_logic(PF, and_result[7:0]);
	assign CF = 0;

	assign_flags u_assign_flags(flags[31:0], OF, DF, SF, ZF, AF, PF, CF);	
endmodule

//-------------------------------------------------------------------------------------
//
// 									 ALU_CLD32
//
//-------------------------------------------------------------------------------------
// Functionality: produces a 32-bit flag with DF = 0
//
// Combinational Delay: 4.2ns
//
module alu_cld (
	output [31:0] cld_result,
	output [31:0] flags
	);

	assign cld_result = 32'h0000_0000;

	wire OF, DF, SF, ZF, AF, PF, CF;  

	assign OF = 0;
	assign DF = 0;
	assign SF = 0;
	assign ZF = 0;
	assign AF = 0;
	assign PF = 0;
	assign CF = 0;

	assign_flags u_assign_flags(flags[31:0], OF, DF, SF, ZF, AF, PF, CF);	
endmodule

//-------------------------------------------------------------------------------------
//
// 									 ALU_CMP32
//
//-------------------------------------------------------------------------------------
// Functionality: does a compare by subtracting, produces flags
//
// Combinational Delay: 4.2ns
//
module alu_cmp (
	output [31:0] cmp_result,
	output [31:0] flags,
	input [31:0] a, b
	);

	wire [31:0] carry_out;
	subtract32 u_subtract32 (cmp_result, carry_out ,a, b);

	wire OF, DF, SF, ZF, AF, PF, CF;  

	OF_logic u_OF_logic(OF, cmp_result[31], a[31], b[31]);
	assign DF = 0;
	assign SF = cmp_result[31];
	ZF_logic u_ZF_logic(ZF, cmp_result[31:0]);
	assign AF = carry_out[3];
	PF_logic u_PF_logic(PF, cmp_result[7:0]);
	assign CF = cmp_result[31];

	assign_flags u_assign_flags(flags[31:0], OF, DF, SF, ZF, AF, PF, CF);	
endmodule

//-------------------------------------------------------------------------------------
//
// 									 ALU_STD32
//
//-------------------------------------------------------------------------------------
// Functionality: produces a 32-bit flag with DF = 1
//
// Combinational Delay: 4.2ns
//
module alu_std (
	output [31:0] std_result,
	output [31:0] flags
	);

	assign std_result = 32'h0000_0000;

	wire OF, DF, SF, ZF, AF, PF, CF;  

	assign OF = 0;
	assign DF = 1;
	assign SF = 0;
	assign ZF = 0;
	assign AF = 0;
	assign PF = 0;
	assign CF = 0;

	assign_flags u_assign_flags(flags[31:0], OF, DF, SF, ZF, AF, PF, CF);	
endmodule

