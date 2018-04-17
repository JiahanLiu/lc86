
module execute (
   input CLK, SET, RST, //not uesd SET/RST

   input EX_V,
   input [31:0] EX_NEIP,
   input [15:0] EX_NCS,
   input [127:0] CONTROL_STORE,
   //pseudo-control store signals not from control store but generated in decode
   input [1:0] EX_de_datasize_all,
   input [2:0] EX_de_aluk_ex, 
   input EX_de_shift_dir_ex, 
   input EX_de_ld_gpr1_ex,
   input EX_de_dcache_write_ex, 
   input [6:0] EX_de_flags_affected_wb,

   input [31:0] EX_A, EX_B, EX_C,
   input [63:0] EX_MM_A, EX_MM_B,

   input [31:0] EX_ADDRESS,

   input [2:0] EX_DR1, EX_DR2, EX_DR3,

   input WB_stall, 

   output WB_V_next,
   output [31:0] WB_NEIP_next, 
   output [15:0] WB_NCS_next,
   output [127:0] WB_CONTROL_STORE_next,

   output [1:0] WB_de_datasize_all_next,
   output WB_ex_ld_gpr1_wb_next,
   output WB_ex_ld_gpr2_wb_next, 
   output WB_ex_dcache_write_wb_next, 
   output [6:0] WB_de_flags_affected_wb_next,

   output [31:0] WB_RESULT_A_next, WB_RESULT_B_next, WB_RESULT_C_next,
   output [31:0] WB_FLAGS_next,
   output [31:0] WB_RESULT_MM_next, 

   output [2:0] WB_DR1_next, WB_DR2_next, WB_DR3_next,

   output DEP_v_ex_ld_gpr1, DEP_v_ex_ld_gpr2, DEP_v_ex_ld_gpr3, Dep_v_ex_ld_seg, Dep_v_ex_ld_mm, Dep_v_ex_dcache_write,

   output WB_ld_latches
);
  //control signals
  `include "./control_store/control_store_wires.v"
  `include "./control_store/control_store_signals.v"

  //internal wires
  //operand_select_ex 
  wire [31:0] b; 
  wire ZF; 
  //cmpxchg_decision_ex
  wire ex_ld_gpr1, ex_ld_gpr2, ex_dcache_write;
  //validate_signal_ex
  wire v_ex_ld_gpr1, v_ex_ld_gpr2, v_cs_ld_gpr3, v_cs_ld_seg, v_cs_ld_mm, v_ex_dcache_write;
  //functional_units
  wire [31:0] alu32_result, alu32_flags, shift_result, shift_flags; 
  wire [63:0] alu64_result; 
  //result_select_ex
  wire [31:0] final_flags; 


  operand_select_ex u_operand_select_ex(b, CLK, CS_IS_CMPS_FIRST_UOP_ALL, CS_IS_CMPS_SECOND_UOP_ALL, EX_A, EX_B);
  cmpxchg_decision_ex u_cmpxchg_decision_ex(ex_ld_gpr1, ex_ld_gpr2, ex_dcache_write, CS_IS_CMPXCHG_EX, EX_de_ld_gpr1_ex, CS_LD_GPR2_WB, EX_de_dcache_write_ex, ZF);
  assign WB_ex_ld_gpr1_wb_next = ex_ld_gpr1;
  assign WB_ex_ld_gpr2_wb_next = ex_ld_gpr2;
  assign WB_ex_dcache_write_wb_next = ex_dcache_write;
  validate_signal_ex u_validate_signal_ex(v_ex_ld_gpr1, v_ex_ld_gpr2, v_cs_ld_gpr3, v_cs_ld_seg, v_cs_ld_mm, v_ex_dcache_write, EX_V, ex_ld_gpr1, ex_ld_gpr2, CS_LD_GPR3_WB, CS_LD_SEG_WB, CS_LD_MM_WB, ex_dcache_write);
  assign DEP_v_ex_ld_gpr1 = v_ex_ld_gpr1;
  assign DEP_v_ex_ld_gpr2 = v_ex_ld_gpr2;
  assign DEP_v_ex_ld_gpr3 = v_cs_ld_gpr3;
  assign Dep_v_ex_ld_seg = v_cs_ld_seg;
  assign Dep_v_ex_ld_mm = v_cs_ld_mm;
  assign Dep_v_ex_dcache_write = v_ex_dcache_write;


  alu32 u_alu32(alu32_result, alu32_flags, EX_A, b, EX_de_aluk_ex);
  alu64 u_alu64(alu64_result, EX_MM_A, EX_MM_B, b, CS_MM_ALUK_EX);
  shifter32 u_shifter32(shift_result, shift_flags, EX_de_shift_dir_ex, EX_A, b, EX_de_datasize_all);
  result_select_ex u_result_select_ex(WB_RESULT_A_next, WB_RESULT_B_next, WB_RESULT_C_next, final_flags, WB_RESULT_MM_next, CS_PASS_A_EX, CS_IS_CMPS_FIRST_UOP_ALL, CS_IS_XCHG_EX, CS_IS_CMPXCHG_EX, CS_MUX_FUNCTION_UNIT_EX, CS_MUX_SP_POP_EX, EX_de_datasize_all, alu32_flags, shift_flags, alu32_result, shift_result, alu64_result, EX_A, EX_B, EX_C);
  assign WB_FLAGS_next = final_flags; 
  assign ZF = final_flags[6];

   //EX latches pass to WB latches
  assign WB_V_next = EX_V;
  assign WB_NEIP_next = EX_NEIP; 
  assign WB_NCS_next = EX_NCS; 
  assign WB_CONTROL_STORE_next = CONTROL_STORE;
  assign WB_de_datasize_all_next = EX_de_datasize_all;

  assign WB_DR1_next = EX_DR1;
  assign WB_DR2_next = EX_DR2;
  assign WB_DR3_next = EX_DR3; 

  //ld_latches
  assign WB_ld_latches = WB_stall;

endmodule
