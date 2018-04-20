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
	input CLK, 
	input PRE,
	input CLR,
	input CS_IS_CMPS_FIRST_UOP_ALL,
	input CS_IS_CMPS_SECOND_UOP_ALL,
	input CS_SAVE_NEIP_WB,
	input CS_SAVE_NCS_WB,
	input CS_PUSH_FLAGS_WB,
	input CS_USE_TEMP_NEIP_WB,
	input CS_USE_TEMP_NCS_WB,
	input [31:0] current_flags,
	input [31:0] WB_RESULT_A,
	input [31:0] WB_NEIP,
	input [15:0] WB_NCS
	);

	wire [31:0] cmps_first_pointer; 
	reg32e$ u_cmps_temp_mem (CLK, WB_RESULT_A, cmps_first_pointer, , CLR, PRE, CS_IS_CMPS_FIRST_UOP_ALL);
	//module reg32e$(CLK, Din, Q, QBAR, CLR, PRE,en);
	
	wire [31:0] temp_neip;
	reg32e$ u_temp_neip (CLK, NEIP, temp_eip, , CLR, PRE, CS_SAVE_NEIP_WB);

	wire [31:0] temp_ncs;
	reg32e$ u_temp_ncs (CLK, NEIP, temp_ncs, , CLR, PRE, CS_SAVE_NCS_WB);

	wire [31:0] post_mux1_data1; 
	mux32_2way u_mux1_data1_pre(post_mux1_data1, WB_RESULT_A, current_flags, CS_PUSH_FLAGS_WB);
	mux32_2way u_mux1_data1_final(data1, post_mux1_data1, cmps_first_pointer, CS_IS_CMPS_SECOND_UOP_ALL);

	mux32_2way u_mux_neip(WB_Final_EIP, WB_NEIP, temp_neip, CS_USE_TEMP_NEIP_WB);

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
	output wb_ld_eip,
	output wb_ld_gpr2, 
	input CS_IS_JNBE_WB,
	input CS_IS_JNE_WB,
	input CS_LD_EIP_WB,
	input CF,
	input ZF,
	input CS_IS_CMOVC_WB,
	input WB_ex_ld_gpr2_wb
	);

	wire cf_not, zf_not, cf_zf_equal_zero;
	wire post_jne_ld_eip; 

	inv1$ not_cf(cf_not, CF);
	inv1$ not_zf(zf_not, ZF);

	mux2$ u_mux_jne(post_jne_ld_eip, CS_LD_EIP_WB, zf_not, CS_IS_JNE_WB);
	and2$ u_cf_zf_zero(cf_zf_equal_zero, cf_not, zf_not);
	mux2$ u_mux_jnbe(wb_ld_eip, post_jne_ld_eip, cf_zf_equal_zero, CS_IS_JNBE_WB);

	mux2$ u_mux_ld_gpr1(wb_ld_gpr2, WB_ex_ld_gpr2_wb, CF, CS_IS_CMOVC_WB); 
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
	output v_cs_ld_mm,
	output v_ex_dcache_write,
	output v_cs_ld_flags,
	output v_wb_ld_eip, 
	output v_cs_ld_cs,
	input WB_V,
	input wb_ld_gpr1,
	input WB_ex_ld_gpr2_wb,
	input CS_LD_GPR3_WB,
	input CS_LD_SEG_WB,
	input CS_LD_MM_WB,
	input WB_ex_dcache_write_wb,
	input CS_LD_FLAGS_WB,
	input wb_ld_eip,
	input CS_LD_CS_WB,
	input CS_IS_CMPS_SECOND_UOP_ALL,
	input WB_de_repne_wb,
	input wb_repne_terminate_all
	);

	and2$ u_and_gpr1(v_wb_ld_gpr1, WB_V, wb_ld_gpr1); 
	and2$ u_and_gpr2(v_ex_ld_gpr2, WB_V, WB_ex_ld_gpr2_wb); 
	and2$ u_and_gpr3(v_cs_ld_gpr3, WB_V, CS_LD_GPR3_WB); 
	and2$ u_and_seg(v_cs_ld_seg, WB_V, CS_LD_SEG_WB); 
	and2$ u_and_mm(v_cs_ld_mm, WB_V, CS_LD_MM_WB); 
	and2$ u_and_dcache(v_ex_dcache_write, WB_V, WB_ex_dcache_write_wb); 
	and2$ u_and_flags(v_cs_ld_flags, WB_V, CS_LD_FLAGS_WB); 

	wire regular_ld_eip, repne_second_uop_cmps;
	or2$ u_second_uop_of_repne(repne_second_uop_cmps, CS_IS_CMPS_SECOND_UOP_ALL, WB_de_repne_wb);
	and2$ u_and_regular_eip(regular_ld_eip, WB_V, wb_ld_eip);
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
	output halt_all,
	output repne_terminate_all,
	input WB_V,
	input CS_IS_HALT_WB,
	input CS_IS_CMPS_SECOND_UOP_ALL,
	input WB_de_repne_wb,
	input ZF,
	input [31:0] WB_RESULT_C
	);

	wire zero_count, second_uop_of_repne, repne_termination_conditions;

	equal_to_zero u_zero_count(zero_count, WB_RESULT_C);
	or2$ u_repne_terminate(repne_termination_conditions, ZF, zero_count);
	and2$ u_second_uop_repne(second_uop_of_repne, CS_IS_CMPS_SECOND_UOP_ALL, WB_de_repne_wb);
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
	output [31:0] current_flags,
	input CLK, 
	input v_cs_ld_flags_wb,
	input CS_POP_FLAGS_WB,
	input [6:0] CS_FLAGS_AFFECTED_WB,
	input [31:0] WB_FLAGS,
	input [31:0] WB_RESULT_A
	);

	wire [31:0] prev_flags, internal_current_flags, and_flags_top, and_flags_bottom, interrupt_flags, next_flags;
	and32_2way u_and_top(and_flags_top, WB_RESULT_A, 32'h00257FD5);
	and32_2way u_and_bottom(and_flags_bottom, internal_current_flags, 32'h00A10000);
	or32_2way u_or_flags(interrupt_flags, and_flags_top, and_flags_bottom);
	mux32_2way u_next_flags(next_flags, internal_current_flags, interrupt_flags, CS_POP_FLAGS_WB);

	assign current_flags = internal_current_flags; 

	reg32e$ flags_register (CLK, internal_current_flags, prev_flags, , 1'b1, 1'b1, v_cs_ld_flags_wb);
	//module reg32e$(CLK, Din, Q, QBAR, CLR, PRE,en);

	genvar i;
	generate
		for(i = 12; i < 32; i = i + 1)
		begin : assign_m
			assign current_flags[i] = prev_flags[i]; 
		end 
	endgenerate
	assign internal_current_flags[9] = current_flags[9];
	assign internal_current_flags[8] = current_flags[8];
	assign internal_current_flags[5] = current_flags[5];
	assign internal_current_flags[3] = current_flags[3];
	assign internal_current_flags[1] = current_flags[1];
	mux2$ u_mux_flag_6(internal_current_flags[11], prev_flags[11], WB_FLAGS[11], CS_FLAGS_AFFECTED_WB[6]);
	mux2$ u_mux_flag_5(internal_current_flags[10], prev_flags[10], WB_FLAGS[10], CS_FLAGS_AFFECTED_WB[5]);
	mux2$ u_mux_flag_4(internal_current_flags[7], prev_flags[7], WB_FLAGS[7], CS_FLAGS_AFFECTED_WB[4]);
	mux2$ u_mux_flag_3(internal_current_flags[6], prev_flags[6], WB_FLAGS[6], CS_FLAGS_AFFECTED_WB[3]);
	mux2$ u_mux_flag_2(internal_current_flags[4], prev_flags[4], WB_FLAGS[4], CS_FLAGS_AFFECTED_WB[2]);
	mux2$ u_mux_flag_1(internal_current_flags[2], prev_flags[2], WB_FLAGS[2], CS_FLAGS_AFFECTED_WB[1]);
	mux2$ u_mux_flag_0(internal_current_flags[0], prev_flags[0], WB_FLAGS[0], CS_FLAGS_AFFECTED_WB[0]);

endmodule // Flags_WB