//-------------------------------------------------------------------------------------
//
// 								operand_select_wb
//
//-------------------------------------------------------------------------------------
// Functionality: selects operands for WB
//
// Combinational Delay: 
//
module operand_select_wb(
	output [31:0] data1,
	output [31:0] WB_Final_EIP,
	output [15:0] WB_Final_CS,
	output [31:0] count,
	input CLK, 
	input PRE,
	input CLR,
	input CS_IS_CMPS_FIRST_UOP_ALL,
	input CS_IS_CMPS_SECOND_UOP_ALL,
	input CS_SAVE_NEIP_WB,
	input CS_SAVE_NCS_WB,
	input CS_PUSH_FLAGS_WB,
	input CS_USE_TEMP_NEIP_WB,
	input mux_not_taken_eip,
	input CS_USE_TEMP_NCS_WB,
	input [31:0] WB_RESULT_A,
	input [31:0] WB_RESULT_C,
	input [31:0] WB_NEIP,
	input [31:0] WB_NEIP_NOT_TAKEN,
	input [15:0] WB_NCS,
	input [31:0] current_flags
	);

	wire [31:0] cmps_first_pointer; 
	reg32e$ u_cmps_temp_mem (CLK, WB_RESULT_A, cmps_first_pointer, , CLR, PRE, CS_IS_CMPS_FIRST_UOP_ALL);
	//module reg32e$(CLK, Din, Q, QBAR, CLR, PRE,en);
	
	wire [31:0] temp_neip;
	reg32e$ u_temp_neip(CLK, WB_NEIP, temp_neip, , CLR, PRE, CS_SAVE_NEIP_WB);

	wire [15:0] temp_ncs;
	wire [31:0] temp_cs_reg_out;
	reg32e$ u_temp_ncs (CLK, {16'h0000,WB_NCS}, temp_cs_reg_out, , CLR, PRE, CS_SAVE_NCS_WB);
	assign temp_ncs = temp_cs_reg_out[15:0];

	wire [31:0] post_mux1_data1; 
	mux32_2way u_mux1_data1_pre(post_mux1_data1, WB_RESULT_A, current_flags, CS_PUSH_FLAGS_WB);
	mux32_2way u_mux1_data1_final(data1, post_mux1_data1, cmps_first_pointer, CS_IS_CMPS_SECOND_UOP_ALL);

	wire [31:0] post_stage1_eip; 
	mux32_2way u_mux_stage1_eip(post_stage1_eip, WB_NEIP, temp_neip, CS_USE_TEMP_NEIP_WB);
	mux32_2way u_mux_neip(WB_Final_EIP, post_stage1_eip, WB_NEIP_NOT_TAKEN, mux_not_taken_eip);

	mux16_2way u_mux_ncs(WB_Final_CS, WB_NCS, temp_ncs, CS_USE_TEMP_NCS_WB);

endmodule // operand_select_wb

//-------------------------------------------------------------------------------------
//
// 								conditional_support_wb
//
//-------------------------------------------------------------------------------------
// Functionality: decides load signals based on condition
//
// Combinational Delay: 
//
module conditional_support_wb(
	output mux_not_taken_eip,
	output wb_ld_gpr2, 
	output wb_branch_taken,
	input CS_IS_JNBE_WB,
	input CS_IS_JNE_WB,
	input [31:0] current_flags,
	input CS_IS_CMOVC_WB,
	input WB_ex_ld_gpr2_wb
	);

	wire CF, ZF;
	assign CF = current_flags[0];
	assign ZF = current_flags[6];

	//jcc

	wire cf_or_zf;
	wire jnbe_not_taken;
	wire jne_not_taken; 

	and2$ u_and_jne(jne_not_taken, ZF, CS_IS_JNE_WB);
	or2$ u_or_cf_zf(cf_or_zf, CF, ZF);
	and2$ u_and_jnbe(jnbe_not_taken, cf_or_zf, CS_IS_JNBE_WB);

	or2$ u_or_final_not_taken_(mux_not_taken_eip, jne_not_taken, jnbe_not_taken); 
	inv1$ u_wb_branch_taken(wb_branch_taken, mux_not_taken_eip);

	//cmovc

	mux2$ u_mux_cmovc(wb_ld_gpr2, WB_ex_ld_gpr2_wb, CF, CS_IS_CMOVC_WB);


endmodule // conditional_support_wb

//-------------------------------------------------------------------------------------
//
// 								validate_signals_wb
//
//-------------------------------------------------------------------------------------
// Functionality: validate signals
//
// Combinational Delay: 
//
module validate_signals_wb(
	output v_wb_ld_gpr1, 
	output v_ex_ld_gpr2,
	output v_cs_ld_gpr3,
	output v_cs_ld_seg,
	output v_d2_ld_mm,
	output v_ex_dcache_write,
	output v_cs_ld_flags,
	output v_cs_ld_eip, 
	output v_cs_ld_cs,
	input WB_V,
	input wb_ld_gpr1,
	input WB_ex_ld_gpr2_wb,
	input CS_LD_GPR3_WB,
	input CS_LD_SEG_WB,
	input WB_d2_ld_mm_wb,
	input WB_ex_dcache_write_wb,
	input CS_LD_FLAGS_WB,
	input cs_ld_eip,
	input CS_LD_CS_WB,
	input CS_IS_CMPS_SECOND_UOP_ALL,
	input WB_d2_repne_wb,
	input wb_repne_terminate_all
	);

	and2$ u_and_gpr1(v_wb_ld_gpr1, WB_V, wb_ld_gpr1); 
	and2$ u_and_gpr2(v_ex_ld_gpr2, WB_V, WB_ex_ld_gpr2_wb); 
	and2$ u_and_gpr3(v_cs_ld_gpr3, WB_V, CS_LD_GPR3_WB); 
	and2$ u_and_seg(v_cs_ld_seg, WB_V, CS_LD_SEG_WB); 
	and2$ u_and_mm(v_d2_ld_mm, WB_V, WB_d2_ld_mm_wb); 
	and2$ u_and_dcache(v_ex_dcache_write, WB_V, WB_ex_dcache_write_wb); 
	and2$ u_and_flags(v_cs_ld_flags, WB_V, CS_LD_FLAGS_WB); 

	wire regular_ld_eip, repne_second_uop_cmps;
	or2$ u_second_uop_of_repne(repne_second_uop_cmps, CS_IS_CMPS_SECOND_UOP_ALL, WB_d2_repne_wb);
	and2$ u_and_regular_eip(regular_ld_eip, WB_V, cs_ld_eip);
	mux2$ u_and_final_eip(v_cs_ld_eip, regular_ld_eip, wb_repne_terminate_all, repne_second_uop_cmps);
	and2$ u_and_cs(v_cs_ld_cs, WB_V, CS_LD_CS_WB);

endmodule // validate_signals_wb

//-------------------------------------------------------------------------------------
//
// 								repne_halt_wb
//
//-------------------------------------------------------------------------------------
// Functionality: do we terminate repne or halt?
//
// Combinational Delay: 
//
module repne_halt_wb(
	output wb_halt_all,
	output wb_repne_terminate_all,
	input WB_V,
	input CS_IS_HALT_WB,
	input CS_IS_CMPS_SECOND_UOP_ALL,
	input WB_d2_repne_wb,
	input [31:0] current_flags,
	input [31:0] WB_RESULT_C
	);

	wire ZF;
	assign ZF = current_flags[6];
	
	wire zero_count, second_uop_of_repne, repne_termination_conditions;

	equal_to_zero u_zero_count(zero_count, WB_RESULT_C);
	or2$ u_repne_terminate(repne_termination_conditions, ZF, zero_count);
	and2$ u_second_uop_repne(second_uop_of_repne, CS_IS_CMPS_SECOND_UOP_ALL, WB_d2_repne_wb);
	and3$ u_terminate_repne(wb_repne_terminate_all, WB_V, repne_termination_conditions, second_uop_of_repne); 

	and2$ u_halt(wb_halt_all, WB_V, CS_IS_HALT_WB); 

endmodule // repne_halt_wb

//-------------------------------------------------------------------------------------
//
// 									Flags_WB
//
//-------------------------------------------------------------------------------------
// Functionality: Updates Affected Flags
//
// Flags is a 32 bit register. Here each flag's location within the register:
// assign flags[11] = OF; 
// assign flags[10] = DF; 
// assign flags[7] = SF; 
// assign flags[6] = ZF; 
// assign flags[4] = AF; 
// assign flags[2] = PF; 
// assign flags[0] = CF; 
//
// Combinational Delay: 
//
module flags_wb(
	output [31:0] final_out_flags,
	input CLK, 
	input v_cs_ld_flags_wb,
	input CS_POP_FLAGS_WB,
	input [6:0] CS_FLAGS_AFFECTED_WB,
	input [31:0] WB_FLAGS,
	input [31:0] WB_RESULT_A
	);

	reg overwrite_ld_flags;

	wire [31:0] prev_flags, calculated_flags, interrupt_flags, final_flags; 
	wire [31:0] and_flags_top, and_flags_bottom;
	
	//get interrupt flags
	and32_2way u_and_top(and_flags_top, WB_RESULT_A, 32'h00257FD5);
	and32_2way u_and_bottom(and_flags_bottom, prev_flags, 32'h00A10000);
	or32_2way u_or_flags(interrupt_flags, and_flags_top, and_flags_bottom);

	//store previous flags
	reg32e$ u_flags_register(.CLK(CLK), .Din(final_flags), .Q(prev_flags), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(overwrite_ld_flags));
	//reg32e$ u_flags_register(.CLK(CLK), .Din(internal_current_flags), .Q(prev_flags), .QBAR(), .CLR(1'b1), .PRE(1'b1), .en(v_cs_ld_flags_wb));
	//module reg32e$(CLK, Din, Q, QBAR, CLR, PRE,en);

	//combine prev flags with alu flags depending on bits affected
	genvar i;
	generate
		for(i = 12; i < 32; i = i + 1)
		begin : assign_m
			assign calculated_flags[i] = prev_flags[i]; 
		end 
	endgenerate
	assign calculated_flags[9] = prev_flags[9];
	assign calculated_flags[8] = prev_flags[8];
	assign calculated_flags[5] = prev_flags[5];
	assign calculated_flags[3] = prev_flags[3];
	assign calculated_flags[1] = prev_flags[1];
	mux2$ u_mux_flag_6(calculated_flags[11], prev_flags[11], WB_FLAGS[11], CS_FLAGS_AFFECTED_WB[6]);
	mux2$ u_mux_flag_5(calculated_flags[10], prev_flags[10], WB_FLAGS[10], CS_FLAGS_AFFECTED_WB[5]);
	mux2$ u_mux_flag_4(calculated_flags[7], prev_flags[7], WB_FLAGS[7], CS_FLAGS_AFFECTED_WB[4]);
	mux2$ u_mux_flag_3(calculated_flags[6], prev_flags[6], WB_FLAGS[6], CS_FLAGS_AFFECTED_WB[3]);
	mux2$ u_mux_flag_2(calculated_flags[4], prev_flags[4], WB_FLAGS[4], CS_FLAGS_AFFECTED_WB[2]);
	mux2$ u_mux_flag_1(calculated_flags[2], prev_flags[2], WB_FLAGS[2], CS_FLAGS_AFFECTED_WB[1]);
	mux2$ u_mux_flag_0(calculated_flags[0], prev_flags[0], WB_FLAGS[0], CS_FLAGS_AFFECTED_WB[0]);

	mux32_2way u_next_flags(final_flags, calculated_flags, interrupt_flags, CS_POP_FLAGS_WB);

	//assign to output
	assign final_out_flags = final_flags; 

endmodule // Flags_WB