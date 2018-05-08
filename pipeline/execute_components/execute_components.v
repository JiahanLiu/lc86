//-------------------------------------------------------------------------------------
//
// 								operand_select_ex
//
//-------------------------------------------------------------------------------------
// Functionality: selects operands for EX
//
// Combinational Delay: 
//
module operand_select_ex(
	output [31:0] b,
	output [31:0] count,
	input CLK,
	input PRE,
	input CLR,
	input CS_IS_CMPS_FIRST_UOP_ALL,
	input CS_IS_CMPS_SECOND_UOP_ALL,
	input CS_REPNE_STEADY_STATE_EX,
	input [31:0] EX_A,
	input [31:0] EX_B,
	input [31:0] EX_C,
	input [31:0] saved_count
	);

	wire [31:0] cmps_first_mem;

	reg32e$ u_cmps_temp_mememory (CLK, EX_A, cmps_first_mem, , CLR, PRE, CS_IS_CMPS_FIRST_UOP_ALL);
	//module reg32e$(CLK, Din, Q, QBAR, CLR, PRE,en);

	mux32_2way u_mux_b(b, EX_B, cmps_first_mem, CS_IS_CMPS_SECOND_UOP_ALL);

	mux32_2way u_mux_count(count, EX_C, saved_count, CS_REPNE_STEADY_STATE_EX);

endmodule // operand_select_ex

//-------------------------------------------------------------------------------------
//
// 								 cmpxchg_decision_ex
//
//-------------------------------------------------------------------------------------
// Functionality: overwrite choices to write to gprs, dcache
//
// Combinational Delay: 
//
module cmpxchg_decision_ex(
	output ex_ld_gpr1,
	output ex_ld_gpr2,
	output ex_dcache_write,
	input CS_IS_CMPXCHG_EX,
	input EX_de_ld_gpr1_ex,
	input CS_LD_GPR2_EX,
	input EX_de_dcache_write_ex,
	input [31:0] alu32_flags
	);
	
	wire ZF;

	assign ZF = alu32_flags[6];

	wire ZF_not;
	wire equal_and_gpr1, equal_and_dcache;
	inv1$ u_not_ZF(ZF_not, ZF);

	and2$ u_equal_and_gpr1(equal_and_gpr1, ZF, EX_de_ld_gpr1_ex);
	and2$ u_equal_and_dcache(equal_and_dcache, ZF, EX_de_dcache_write_ex);

	mux2$ u_mux_gpr1(ex_ld_gpr1, EX_de_ld_gpr1_ex, equal_and_gpr1, CS_IS_CMPXCHG_EX);

	mux2$ u_mux_gpr2(ex_ld_gpr2, CS_LD_GPR2_EX, ZF_not, CS_IS_CMPXCHG_EX); 

	mux2$ u_mux_dcache(ex_dcache_write, EX_de_dcache_write_ex, equal_and_dcache, CS_IS_CMPXCHG_EX);

endmodule // cmpxchg_decision_ex

//-------------------------------------------------------------------------------------
//
// 								 validate_signal_ex
//
//-------------------------------------------------------------------------------------
// Functionality: validates signals
//
// Combinational Delay: 
//
module validate_signal_ex(
	output v_ex_ld_gpr1,
	output v_ex_ld_gpr2,
	output v_cs_ld_gpr3,
	output v_cs_ld_seg,
	output v_d2_ld_mm,
	output v_ex_dcache_write,
	input EX_V,
	input ex_ld_gpr1,
	input ex_ld_gpr2,
	input CS_LD_GPR3_WB,
	input CS_LD_SEG_WB,
	input d2_ld_mm_wb,
	input ex_dcache_write
	);

	and2$ u_and_gpr1(v_ex_ld_gpr1, EX_V, ex_ld_gpr1);
	and2$ u_and_gpr2(v_ex_ld_gpr2, EX_V, ex_ld_gpr2);
	and2$ u_and_gpr3(v_cs_ld_gpr3, EX_V, CS_LD_GPR3_WB);
	and2$ u_and_seg(v_cs_ld_seg, EX_V, CS_LD_SEG_WB);
	and2$ u_and_mm(v_d2_ld_mm, EX_V, d2_ld_mm_wb);
	and2$ u_and_dcache(v_ex_dcache_write, EX_V, ex_dcache_write);

endmodule // validate_signal_ex

module functional_unit_ex(
	output [31:0] alu32_result,
	output [31:0] alu32_flags,
	output [63:0] alu64_result,
	output [31:0] shift_result,
	output [31:0] shift_flags,
	output [31:0] count_minus_one,
	output [31:0] stack_pointer_pop,
	output [31:0] cmps_pointer_updated,
	input [2:0] EX_d2_aluk_ex,
	input [1:0] EX_d2_datasize_all,
	input [31:0] EX_A,
	input [31:0] EX_B,
	input [31:0] b,
	input [31:0] EX_C,
	input [31:0] count,
	input [31:0] flags_dataforwarded,
	input [2:0] CS_ALUK_D2,
	input [63:0] EX_MM_A,
	input [63:0] EX_MM_B
	);

	wire [31:0] pop_increment;
	wire CF_dataforwarded, AF_dataforwarded; 
	assign CF_dataforwarded = flags_dataforwarded[0];
	assign AF_dataforwarded = flags_dataforwarded[4];
	assign DF_dataforwarded = flags_dataforwarded[10];

 	alu32 u_alu32(alu32_result, alu32_flags, EX_A, b, EX_d2_aluk_ex, EX_d2_datasize_all, CF_dataforwarded, AF_dataforwarded);
  	alu64 u_alu64(alu64_result, EX_MM_A, EX_MM_B, b, CS_ALUK_D2);
  	shifter32 u_shifter32(shift_result, shift_flags, EX_d2_aluk_ex[0], EX_A, EX_B, EX_d2_datasize_all, flags_dataforwarded);
 	adder32 u_count_minus_one(count_minus_one, ,count, 32'hffff_ffff);
 	mux32_4way u_pop_mux(pop_increment, 32'h0000_0001, 32'h0000_0002, 32'h0000_0004, 32'h0000_0008, EX_d2_datasize_all);
 	adder32 u_stack_add(stack_pointer_pop, ,EX_C, pop_increment);

 	wire [31:0] cmps_inc_amount, cmps_dec_amount, cmps_inc_pointer, cmps_dec_pointer;
 	mux32_4way u_inc_mux(cmps_inc_amount, 32'h0000_0001, 32'h0000_0002, 32'h0000_0004, 32'h0000_0008, EX_d2_datasize_all);
 	mux32_4way u_dec_mux(cmps_dec_amount, 32'hFFFF_FFFF, 32'hFFFF_FFFE, 32'hFFFF_FFFC, 32'hFFFF_FFF8, EX_d2_datasize_all);
 	adder32 u_cmps_pointer_increment(cmps_inc_pointer, ,EX_B, cmps_inc_amount); 
 	adder32 u_cmps_pointer_decrement(cmps_dec_pointer, ,EX_B, cmps_dec_amount); 
 	mux32_2way u_cmps_pointer(cmps_pointer_updated, cmps_inc_pointer, cmps_dec_pointer, DF_dataforwarded);

endmodule // functional_unit_ex

module stall_and_bubble_ex(
	output WB_ld_latches,
	output WB_V_next,
	input WB_Stall,
	input WB_de_repne_all,
	input EX_V,
	input wb_repne_terminate_all
	);

	inv1$ not_wb_stall(WB_ld_latches, WB_Stall);

	wire wb_repne_terminate_all_not;
	wire valid_terminate_not;
	
	inv1$ not_wb_repne_terminate_all(wb_repne_terminate_all_not, wb_repne_terminate_all);
	and2$ and_terminate(valid_terminate_not, EX_V, wb_repne_terminate_all_not);
	mux2$ u_mux_wb_valid(WB_V_next, EX_V, valid_terminate_not, WB_de_repne_all);

endmodule // stall_and_bubble_ex

module repne_support(
	output [31:0] repne_count,
	input [31:0] count,
	input [31:0] count_minus_one
	);

	wire repne_zero_terminate;

	equal_to_zero u_zero_count(repne_zero_terminate, count);
	mux32_2way u_mux_repne_count(repne_count, count_minus_one, count, repne_zero_terminate);

endmodule // repne_support

//-------------------------------------------------------------------------------------
//
// 								 result_select_ex
//
//-------------------------------------------------------------------------------------
// Functionality: selects results
//
// Combinational Delay: 
//
module result_select_ex(
	output [31:0] WB_RESULT_A_next,
	output [31:0] WB_RESULT_B_next,
	output [31:0] WB_RESULT_C_next,
	output [31:0] WB_FLAGS_next,
	output [63:0] WB_RESULT_MM_next,
	input CS_IS_ALU32_EX,
	input CS_IS_CMPS_FIRST_UOP_ALL,
	input CS_IS_XCHG_EX,
	input CS_PASS_A_EX,
	input CS_IS_CMPXCHG_EX,
	input CS_IS_CMPS_SECOND_UOP_ALL,
	input CS_MUX_SP_POP_EX,
	input CS_IS_ALU32_FLAGS_EX,
	input CS_ALU_TO_B_EX,
	input CS_MUX_CMPS_POINTER_EX,
	input [31:0] shift_result,
	input [31:0] EX_C,
	input [31:0] EX_A,
	input [31:0] EX_B,
	input [31:0] alu32_result,
	input [31:0] stack_pointer_pop,
	input [31:0] cmps_pointer_updated,
	input [31:0] count_minus_one,
	input [31:0] shift_flags,
	input [31:0] alu32_flags,
	input [63:0] alu64_result
	);
	wire choose_a_as_b_signal, choose_b_as_a_signal;

	or2$ u_a_as_b(choose_a_as_b_signal, CS_IS_CMPS_FIRST_UOP_ALL, CS_IS_XCHG_EX);
	or2$ u_b_as_a(choose_b_as_a_signal, CS_IS_CMPXCHG_EX, CS_IS_XCHG_EX);
	//WB_RESULT_A
	wire [31:0] post_mux_c, post_mux_a, post_mux_b, post_mux_cmps;
	mux32_2way u_mux_c(post_mux_c, shift_result, EX_C, CS_IS_CMPXCHG_EX);
	mux32_2way u_mux_a(post_mux_a, post_mux_c, EX_A, CS_PASS_A_EX);
	mux32_2way u_mux_b(post_mux_b, post_mux_a, EX_B, choose_a_as_b_signal);
	mux32_2way u_mux_cmps(post_mux_cmps, post_mux_b, cmps_pointer_updated, CS_MUX_CMPS_POINTER_EX);
	mux32_2way u_mux_resultA(WB_RESULT_A_next, post_mux_cmps, alu32_result, CS_IS_ALU32_EX);
	//WB_RESULT_B
	wire [31:0] post_stage1_b, post_stage2_b; 
	mux32_2way u_mux_stage1B(post_stage1_b, EX_B, EX_A, choose_b_as_a_signal);
	mux32_2way u_mux_stage2B(post_stage2_b, post_stage1_b, alu32_result, CS_ALU_TO_B_EX);
	mux32_2way u_mux_resultB(WB_RESULT_B_next, post_stage2_b, cmps_pointer_updated, CS_MUX_CMPS_POINTER_EX);
	//WB_RESULT_C
	wire [31:0] post_stack_pointer;
	wire pass_count_minus_one; 
	or2$ u_or_pass_count_minus_one(pass_count_minus_one, CS_IS_CMPS_FIRST_UOP_ALL, CS_IS_CMPS_SECOND_UOP_ALL);
	mux32_2way u_mux_increment_size(post_stack_pointer, EX_C, stack_pointer_pop, CS_MUX_SP_POP_EX);
	mux32_2way u_mux_resultC(WB_RESULT_C_next, post_stack_pointer, count_minus_one, pass_count_minus_one);

	mux32_2way u_mux_flags(WB_FLAGS_next, shift_flags, alu32_flags, CS_IS_ALU32_FLAGS_EX);

	assign WB_RESULT_MM_next = alu64_result;

endmodule // result_select_ex

