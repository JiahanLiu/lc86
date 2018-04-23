module writeback (
   input CLK, PRE, CLR, //not used SET/RST

   input WB_V,
   input [31:0] WB_NEIP,
   input [15:0] WB_NCS,
   input [127:0] CONTROL_STORE,
   //pseudo-control store signals not from control store but generated in decode
   input [1:0] WB_d2_datasize_all,
   input WB_ex_ld_gpr1_wb,
   input WB_ex_ld_gpr2_wb,
   input WB_ex_dcache_write_wb,
   input WB_d2_repne_wb, 

   input [31:0] WB_RESULT_A, 
   input [31:0] WB_RESULT_B, 
   input [31:0] WB_RESULT_C,
   input [31:0] WB_FLAGS,
   input [63:0] WB_RESULT_MM,

   input [2:0] WB_DR1,
   input [2:0] WB_DR2,
   input [2:0] WB_DR3,
   input [31:0] WB_ADDRESS,

   input In_write_ready, 

   output [2:0] WB_Final_DR1,
   output [2:0] WB_Final_DR2,
   output [2:0] WB_Final_DR3,
   output [31:0] WB_Final_data1,
   output [31:0] WB_Final_data2,
   output [31:0] WB_Final_data3,
   output WB_Final_ld_gpr1,
   output WB_Final_ld_gpr2,
   output WB_Final_ld_gpr3,
   output [1:0] WB_Final_datasize,
   output WB_Final_ld_seg, 
   output [63:0] WB_Final_MM_Data,
   output WB_Final_ld_mm, 
   output [31:0] WB_Final_EIP, 
   output WB_Final_ld_eip, 
   output [15:0] WB_Final_CS, 
   output WB_Final_ld_cs, 
   output [31:0] WB_Final_Flags,
   output WB_Final_ld_flags,
   output [63:0] WB_Final_Dcache_Data,
   output [31:0] WB_Final_Dcache_address,

   output DEP_v_wb_ld_gpr1,
   output DEP_v_wb_ld_gpr2,
   output DEP_v_wb_ld_gpr3,
   output DEP_v_wb_ld_seg,
   output DEP_v_wb_ld_mm,
   output DEP_v_wb_dcache_write,

   output wb_halt_all, 
   output wb_repne_terminate_all,
   output WB_stall,
   
   output [31:0] flags_dataforwarded,
   output [31:0] count_dataforwarded
   );

  //control signals
  `include "./control_store/control_store_wires.v"
  `include "./control_store/control_store_signals.v"

   //internal wires
   //operand_select_wb
   wire [31:0] data1, count; 
   //conditional_support_wb
   wire wb_ld_eip, wb_ld_gpr2;
   //validate_signals_wb
   wire v_wb_ld_gpr1, v_ex_ld_gpr2, v_cs_ld_gpr3, v_cs_ld_seg, v_cs_ld_mm, 
      v_ex_dcache_write, v_cs_ld_flags, v_wb_ld_eip, v_cs_ld_cs;
   //repne_halt_wb
   wire ZF; 
   //flags_wb
   wire [31:0] current_flags;
   wire v_cs_ld_flags_wb; 
   //outputs
   wire [63:0] data1_64; //64 because dcache data-in port is 64 bits incase the input is mm 
   //stall
   wire In_write_ready_not;
   operand_select_wb u_operand_select_wb(data1, WB_Final_EIP, WB_Final_CS, count, CLK, PRE, CLR,
      CS_IS_CMPS_FIRST_UOP_ALL, CS_IS_CMPS_SECOND_UOP_ALL, CS_SAVE_NEIP_WB, CS_SAVE_NCS_WB,
      CS_PUSH_FLAGS_WB, CS_USE_TEMP_NEIP_WB, CS_USE_TEMP_NCS_WB, WB_RESULT_A, WB_RESULT_C, WB_NEIP,
      WB_NCS, current_flags);

   conditional_support_wb u_conditional_support_wb(wb_ld_eip, wb_ld_gpr2, CS_IS_JNBE_WB, 
      CS_IS_JNE_WB, CS_LD_EIP_WB, CF, ZF, CS_IS_CMOVC_WB, WB_ex_ld_gpr2_wb);
   validate_signals_wb u_validate_signals_wb(v_wb_ld_gpr1, v_ex_ld_gpr2, v_cs_ld_gpr3,
      v_cs_ld_seg, v_cs_ld_mm, v_ex_dcache_write, v_cs_ld_flags, v_wb_ld_eip, v_cs_ld_cs,
      WB_V, WB_ex_ld_gpr1_wb, wb_ld_gpr2, CS_LD_GPR3_WB, CS_LD_SEG_WB, CS_LD_MM_WB, 
      WB_ex_dcache_write_wb, CS_LD_FLAGS_WB, wb_ld_eip,CS_LD_CS_WB,CS_IS_CMPS_SECOND_UOP_ALL,
      WB_d2_repne_wb, wb_repne_terminate_all);
   assign DEP_v_wb_ld_gpr1 = v_wb_ld_gpr1;
   assign DEP_v_wb_ld_gpr2 = v_ex_ld_gpr2;
   assign DEP_v_wb_ld_gpr3 = v_cs_ld_gpr3;
   assign DEP_v_wb_ld_seg = v_cs_ld_seg;
   assign DEP_v_wb_ld_mm = v_cs_ld_mm;
   assign DEP_v_wb_dcache_write = v_ex_dcache_write;

   result_select_ex u_result_select_ex(WB_RESULT_A_next, WB_RESULT_B_next, WB_RESULT_C_next, WB_FLAGS_next, 
      WB_RESULT_MM_next, CS_IS_ALU32_EX, CS_IS_CMPS_FIRST_UOP_ALL, CS_IS_XCHG_EX,
      CS_PASS_A_EX, CS_IS_CMPXCHG_EX, CS_IS_CMPS_SECOND_UOP_ALL, CS_MUX_SP_POP_EX,
      CS_IS_ALU32_FLAGS_EX, shift_result, EX_C, EX_A, EX_B, alu32_result, stack_pointer_pop,
      count_minus_one, shift_flags, alu32_flags, alu64_result);

   flags_wb u_flags_wb(current_flags, CLK, v_cs_ld_flags_wb, CS_POP_FLAGS_WB, 
      CS_FLAGS_AFFECTED_WB, WB_FLAGS, WB_RESULT_A);

   //regfile32
   assign WB_Final_DR1 = WB_DR1;
   assign WB_Final_DR2 = WB_DR2;
   assign WB_Final_DR3 = WB_DR3; 
   assign WB_Final_data1 = data1;
   assign WB_Final_data2 = WB_RESULT_B;
   assign WB_Final_data3 = WB_RESULT_C;
   assign WB_Final_ld_gpr1 = v_wb_ld_gpr1; 
   assign WB_Final_ld_gpr2 = v_ex_ld_gpr2;
   assign WB_Final_ld_gpr3 = v_cs_ld_gpr3; 
   assign WB_Final_datasize = WB_d2_datasize_all;
   //segfile
   assign WB_Final_ld_seg = v_cs_ld_seg; 
   //regfile64
   assign WB_Final_MM_Data = WB_RESULT_MM; 
   assign WB_Final_ld_mm = v_cs_ld_mm; 
   //EIP register
   assign WB_Final_ld_eip = v_wb_ld_eip;
   //CS register
   assign WB_Final_ld_cs = v_cs_ld_cs;
   //Flags register
   assign WB_Final_Flags = current_flags;
   assign WB_Final_ld_flags = v_cs_ld_flags;
   //DCACHE outputs
   assign data1_64 = {{32{1'b0}}, data1};
   mux64_2way u_dache_data_in(WB_Final_Dcache_Data, data1_64, WB_RESULT_MM, CS_MM_MEM_WB);
   assign WB_Final_Dcache_Data = data1; 
   assign WB_Final_Dcache_Address = WB_ADDRESS; 

   //stall logic
   inv1$ u_not_write_ready(In_write_ready_not, In_write_ready);
   and2$ u_wb_stall(WB_stall, v_ex_dcache_write, In_write_ready_not);

   //dataforward
   assign flags_dataforwarded = current_flags;
   assign count_dataforwarded = count;

endmodule
