module alu (alu_out, flags, a, b, op);
	output [31:0] alu_out;
	output [31:0] flags;
	input [31:0] a, b;
	input [2:0] op;

	wire [31:0] adder_result, or_result, not_result, xchg_result, and_result, daa_result, cmp_result, chk_if_zero_result;
	wire [6:0] adder_flags, or_flags, not_flags, xchg_flags, and_flags, daa_flags, cmp_flags, chk_if_zero_flags;

	assign or_result = 32'h00000000;
	assign not_result = 32'h00000000;
	assign xchg_result = 32'h00000000;
	assign and_result = 32'h00000000;
	assign daa_result = 32'h00000000;
	assign cmp_result = 32'h00000000;
	assign chk_if_zero_result = 32'h00000000;

	assign or_flags = 32'h00000000;
	assign not_flags = 32'h00000000;
	assign xchg_flags = 32'h00000000;
	assign and_flags = 32'h00000000;
	assign daa_flags = 32'h00000000;
	assign cmp_flags = 32'h00000000;
	assign chk_if_zero_flags = 32'h00000000;

	adder32 alu_adder (adder_result, adder_flags, a, b);

	mux32_8way out_selection(alu_out, adder_result, or_result, not_result, xchg_result, and_result, daa_result, cmp_result, chk_if_zero_result, op[0], op[1], op[2]);
endmodule // alu

module alu_adder (adder_result, flags, a, b);
	output [31:0] adder_result;
	output [31:0] flags;
	input [31:0] a, b;

	wire [31:0] adder_carry; 
	wire CF, SF, AF, OF, PF, ZF; 

	adder32 u_adder32(adder_result, adder_carry, a, b);  
	
	assign CF = adder_carry[31];
	assign SF = adder_result[31];
	assign AF = adder_carry[3];

	//ZF
	wire ZF_31_28, ZF_27_24, ZF_23_20, ZF_19_16, ZF_15_12, ZF_11_8, ZF_7_4, ZF_3_0;
	wire ZF_31_16, ZF_15_0; 
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
	or4$ u_or_zf_31_16(ZF_31_16, ZF_31_24, ZF_31_28, ZF_27_24, ZF_19_16);
	or4$ u_or_zf_15_0(ZF_15_0, ZF_15_12, ZF_11_8, ZF_7_4, ZF_3_0);
	//layer 3
	or2$ u_or_zf_31_0(ZF, ZF_31_16, ZF_15_0);

	//OF
	wire xor_result_a, xnor_a_b; 
	xor2$ u_xor_of(xor_result_a, adder_result[31], a[31]);
	xnor2$ u_xnor_of(xnor_a_b, a[31], b[31]);
	and2$ u_xand_of (OF, xor_result_a, xnor_a_b);

	//PF
	wire PF_7_6, PF_5_4, PF_3_2, PF_1_0;
	wire PF_7_4, PF_3_0;

	xor2$ u_xor2_pf_7_6 (PF_7_6, adder_result[7], adder_result[6]);
	xor2$ u_xor2_pf_5_4 (PF_5_4, adder_result[5], adder_result[4]);
	xor2$ u_xor2_pf_3_2 (PF_3_2, adder_result[3], adder_result[2]);
	xor2$ u_xor2_pf_1_0 (PF_1_0, adder_result[1], adder_result[0]);

	xor2$ u_xor2_pf_7_4 (PF_7_4, PF_7_6, PF_5_4);
	xor2$ u_xor2_pf_3_0 (PF_3_0, PF_3_2, PF_1_0);

	xor2$ u_xor2_pf_7_0 (PF, PF_7_4, PF_3_0);	

	//assign to flag output
	assign flags[11] = OF; 
	assign flags[10] = 0; 
	assign flags[7] = SF; 
	assign flags[6] = ZF; 

	assign flags[4] = AF; 
	assign flags[2] = PF; 
	assign flags[0] = CF; 	

	assign flags[31:12] = 20'h00000;
	assign flags[9:8] = 2'b00;
	assign flags[5] = 1'b0; 
	assign flags[3] = 1'b0; 
	assign flags[1] = 1'b0; 	

endmodule

