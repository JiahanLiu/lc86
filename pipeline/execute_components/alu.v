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
// Combinational Delay:
//
module alu32 (
	output [31:0] alu_out,
	output [31:0] flags,
	input [31:0] a, b,
	input [2:0] op,
	input [1:0] datasize,
	input CF_dataforwarded,
	input AF_dataforwarded
	);

	wire [31:0] adder_result, or_result, not_result, daa_result, and_result, cld_result, cmp_result, std_result;
	wire [31:0] adder_flags, or_flags, not_flags, daa_flags, and_flags, cld_flags, cmp_flags, std_flags;

	alu_adder u_alu_adder (adder_result, adder_flags, a, b, datasize);
	alu_or u_alu_or (or_result, or_flags, a, b, datasize);
	alu_not u_alu_not (not_result, not_flags, a);
	alu_daa u_alu_daa (daa_result, daa_flags, a, CF_dataforwarded, AF_dataforwarded);
	alu_and u_alu_and (and_result, and_flags, a, b, datasize);
	alu_cld u_alu_cld (cld_result, cld_flags);
	alu_cmp u_alu_cmp (cmp_result, cmp_flags, b, a, datasize); //inverted because of how Nelson gives me the data
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
// Combinational Delay: 
//
module alu_adder (adder_result, flags, a, b, datasize);
	output [31:0] adder_result;
	output [31:0] flags;
	input [31:0] a, b;
	input [1:0] datasize;

	wire [31:0] adder_carry; 
	adder32 u_adder32(adder_result, adder_carry, a, b);  

	wire OF, DF, SF, ZF, AF, PF, CF; 

	OF_logic u_OF_logic(OF, adder_result, a, b, datasize);
	assign DF = 0;
	SF_logic u_SF_logic(SF, adder_result, datasize);
	ZF_logic u_ZF_logic(ZF, adder_result[31:0], datasize);
	assign AF = adder_carry[3];
	PF_logic u_PF_logic(PF, adder_result[7:0]);
	CF_logic u_CF_logic(CF, adder_carry, datasize);

	assign_flags u_assign_flags(flags[31:0], OF, DF, SF, ZF, AF, PF, CF);	

endmodule

//-------------------------------------------------------------------------------------
//
// 									  ALU_OR32
//
//-------------------------------------------------------------------------------------
// Functionality: 32-bitwise OR, produces flags
//
// Combinational Delay: 
//
module alu_or (
	output [31:0] or_result,
	output [31:0] flags,
	input [31:0] a, b,
	input [1:0] datasize
	);

	or32_2way u_or32_2way(or_result, a, b);

	wire OF, DF, SF, ZF, AF, PF, CF;  

	assign OF = 0;
	assign DF = 0;
	SF_logic u_SF_logic(SF, or_result, datasize);
	ZF_logic u_ZF_logic(ZF, or_result, datasize);
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
// Combinational Delay: 
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
// Combinational Delay: 
//
module alu_daa (
	output [31:0] daa_result,
	output [31:0] flags,
	input [31:0] a,
	input CF_dataforwarded,
	input AF_dataforwarded
	);

	wire low_or, high_or0, high_or1, low_and, high_and0, high_and1, low_needs_daa;
	wire high_needs_daa0, high_needs_daa1, high_needs_daa; 
	wire [31:0] low_sum, high_sum, AL_part1, AL_part2, low_carry;
	wire carry_low; 

	//needs daa low
	or2$ u_or_low(low_or, a[2], a[1]);
	and2$ u_and_low(low_and, a[3], low_or);
	or2$ u_or_low_needs_daa(low_needs_daa, low_and, AF_dataforwarded); 
	//needs daa high 0
	or2$ u_or_high0(high_or0, AL_part1[6], AL_part1[5]);
	and2$ u_and_high0(high_and0, AL_part1[7], high_or0); 
	or2$ u_or_high_needs_daa0(high_needs_daa0, high_and0, CF_dataforwarded); 
	//needs daa high 1
	or2$ u_or_high1(high_or1, a[6], a[5]);
	and2$ u_and_high1(high_and1, a[7], high_or1); 
	or2$ u_or_high_needs_daa1(high_needs_daa1, high_and1, CF_dataforwarded); 
	//final daa high
	or2$ u_high_needs_daa_final(high_needs_daa, high_needs_daa0, high_needs_daa1);

	adder32 u_add_low(low_sum, low_carry, a, 32'h00000006);
	mux32_2way u_mux_sum_low(AL_part1, a, low_sum, low_needs_daa);
	assign carry_low = low_carry[3];
	adder32 u_add_high(high_sum, ,AL_part1, 32'h00000060); 
	mux32_2way u_mux_sum_high(AL_part2, AL_part1, high_sum, high_needs_daa);

	wire CF_or; 
	wire CF_part1, CF_part2; 
	or2$ u_or_cf(CF_or, CF_dataforwarded, carry_low);
	mux2$ u_mux_CF_low(CF_part1, CF_dataforwarded, CF_or, low_needs_daa);
	mux2$ u_mux_CF_high(CF_part2, 1'b0, 1'b1, high_needs_daa);

	wire AF_part2;
	mux2$ u_mux_AF(AF_part2, 1'b0, 1'b1, low_needs_daa);	

	wire OF, DF, SF, ZF, AF, PF, CF;  

    assign daa_result[31:8] = 24'b0;
    assign daa_result[7:0] = AL_part2; 
	assign OF = 0;
	assign DF = 0;
	assign SF = 0; //bcd is unsigned, vol1, page 80
	ZF_logic_daa u_ZF_logic_daa(ZF, daa_result[7:0]);
	assign AF = AF_part2;
	PF_logic u_PF_logic(PF, daa_result[7:0]);
	assign CF = CF_part2;

	assign_flags u_assign_flags(flags[31:0], OF, DF, SF, ZF, AF, PF, CF);	
endmodule

//-------------------------------------------------------------------------------------
//
// 									  ALU_AND32
//
//-------------------------------------------------------------------------------------
// Functionality: 32-bitwise AND, produces flags
//
// Combinational Delay: 
//
module alu_and (
	output [31:0] and_result,
	output [31:0] flags,
	input [31:0] a, b,
	input [1:0] datasize
	);

	and32_2way and32_2way (and_result, a, b);

	wire OF, DF, SF, ZF, AF, PF, CF;  

	assign OF = 0;
	assign DF = 0;
	SF_logic u_SF_logic(SF, and_result, datasize);
	ZF_logic u_ZF_logic(ZF, and_result, datasize);
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
// Combinational Delay: 
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
// Combinational Delay: 
//
module alu_cmp (
	output [31:0] cmp_result,
	output [31:0] flags,
	input [31:0] a, b,
	input [1:0] datasize
	);

	wire [31:0] carry_out;
	subtract32 u_subtract32 (cmp_result, carry_out ,a, b);

	wire OF, DF, SF, ZF, AF, PF, CF;  

	OF_logic u_OF_logic(OF, cmp_result, a, b, datasize);
	assign DF = 0;
	SF_logic u_SF_logic(SF, cmp_result, datasize);
	ZF_logic u_ZF_logic(ZF, cmp_result, datasize);
	assign AF = carry_out[3];
	PF_logic u_PF_logic(PF, cmp_result[7:0]);
	assign CF = carry_out[31];

	assign_flags u_assign_flags(flags[31:0], OF, DF, SF, ZF, AF, PF, CF);	
endmodule

//-------------------------------------------------------------------------------------
//
// 									 ALU_STD32
//
//-------------------------------------------------------------------------------------
// Functionality: produces a 32-bit flag with DF = 1
//
// Combinational Delay: 
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

