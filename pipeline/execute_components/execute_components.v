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
	input CLK,
	input CS_IS_CMPS_FIRST_UOP_ALL,
	input CS_IS_CMPS_SECOND_UOP_ALL,
	input [31:0] EX_A,
	input [31:0] EX_B
	);

	wire [31:0] cmps_first_mem;

	reg32e$ u_cmps_temp_mem (CLK, EX_A, cmps_first_mem, , 1'b1, 1'b1, CS_IS_CMPS_FIRST_UOP_ALL);
	//module reg32e$(CLK, Din, Q, QBAR, CLR, PRE,en);

	mux32_2way u_mux_b(b, EX_B, cmps_first_mem, CS_IS_CMPS_SECOND_UOP_ALL);

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
	input CS_LD_GPR2_WB,
	input EX_de_dcache_write_ex,
	input ZF
	);

	wire ZF_not;
	wire equal_and_gpr1, equal_and_dcache;
	inv1$ u_not_ZF(ZF_not, ZF);

	and2$ u_equal_and_gpr1(equal_and_gpr1, ZF, EX_de_ld_gpr1_ex);
	and2$ u_equal_and_dcache(equal_and_dcache, ZF, EX_de_dcache_write_ex);

	mux2$ u_mux_gpr1(ex_ld_gpr1, EX_de_ld_gpr1_ex, equal_and_gpr1, CS_IS_CMPXCHG_EX);

	mux2$ u_mux_gpr2(ex_ld_gpr2, CS_LD_GPR2_WB, ZF_not, CS_IS_CMPXCHG_EX); 

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
	output v_cs_ld_mm,
	output v_ex_dcache_write,
	input EX_V,
	input ex_ld_gpr1,
	input ex_ld_gpr2,
	input CS_LD_GPR3_WB,
	input CS_LD_SEG_WB,
	input CS_LD_MM_WB,
	input ex_dcache_write
	);

	and2$ u_and_gpr1(v_ex_ld_gpr1, EX_V, ex_ld_gpr1);
	and2$ u_and_gpr2(v_ex_ld_gpr2, EX_V, ex_ld_gpr2);
	and2$ u_and_gpr3(v_cs_ld_gpr3, EX_V, CS_LD_GPR3_WB);
	and2$ u_and_seg(v_cs_ld_seg, EX_V, CS_LD_SEG_WB);
	and2$ u_and_mm(v_cs_ld_mm, EX_V, CS_LD_MM_WB);
	and2$ u_and_dcache(v_ex_dcache_write, EX_V, ex_dcache_write);

endmodule // validate_signal_ex

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
	input CS_PASS_A_EX,
	input CS_IS_CMPS_FIRST_UOP_ALL,
	input CS_IS_XCHG_EX,
	input CS_IS_CMPXCHG_EX,
	input CS_MUX_FUNCTION_UNIT_EX,
	input CS_MUX_SP_POP_EX,
	input [1:0] EX_de_datasize_all,
	input [31:0] alu32_flags,
	input [31:0] shift_flags,
	input [31:0] alu32_result,
	input [31:0] shift_xchg_result,
	input [63:0] alu64_result,
	input [31:0] EX_A,
	input [31:0] EX_B,
	input [31:0] EX_C
	);

	wire choose_a_as_b_signal, choose_b_as_a_signal;
	wire [31:0] post_mux_functional_unit, post_mux_c, post_mux_a; 
	wire [31:0] increment_value, new_stack_pointer;

	or2$ u_a_as_b(choose_a_as_b_signal, CS_IS_CMPS_FIRST_UOP_ALL, CS_IS_XCHG_EX);
	or2$ u_b_as_a(choose_b_as_a_signal, CS_IS_CMPXCHG_EX, CS_IS_XCHG_EX);

	mux32_2way u_mux_functional_unit(post_mux_functional_unit, alu32_result, shift_xchg_result, CS_MUX_FUNCTION_UNIT_EX);
	mux32_2way u_mux_resultA_c(post_mux_c, post_mux_functional_unit, EX_C, CS_IS_CMPXCHG_EX);
	mux32_2way u_mux_resultA_a(post_mux_a, post_mux_c, EX_A, CS_PASS_A_EX);
	mux32_2way u_mux_resultA_b(WB_RESULT_A_next, post_mux_a, EX_B, choose_a_as_b_signal);

	mux32_2way u_mux_resultB(WB_RESULT_B_next, EX_B, EX_A, choose_b_as_a_signal);

	mux32_2way u_mux_increment_size(increment_value, 32'h00000002, 32'h00000004, EX_de_datasize_all[1]);
	adder32 stack_adder(new_stack_pointer, , EX_C, increment_value);
	mux32_2way u_mux_resultC(WB_RESULT_C_next, EX_C, new_stack_pointer, CS_MUX_SP_POP_EX);

	mux32_2way u_mux_flags(WB_FLAGS_next, alu32_flags, shift_flags, CS_MUX_FUNCTION_UNIT_EX);

	assign WB_RESULT_MM_next = alu64_result;

endmodule // result_select_ex