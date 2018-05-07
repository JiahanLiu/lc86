module writeback (
   input CLK, PRE, CLR, //not used SET/RST

   input WB_V,
   input [31:0] WB_NEIP_NOT_TAKEN,
   input [31:0] WB_NEIP,
   input [15:0] WB_NCS,
   input [127:0] CONTROL_STORE,
   //pseudo-control store signals not from control store but generated in decode
   input [1:0] WB_d2_datasize_all,
   input WB_ex_ld_gpr1_wb,
   input WB_ex_ld_gpr2_wb,
   input WB_d2_ld_mm_wb,
   input WB_ex_dcache_write_wb,
   input WB_d2_repne_wb, 

   input [31:0] WB_RESULT_A, 
   input [31:0] WB_RESULT_B, 
   input [31:0] WB_RESULT_C,
   input [31:0] WB_FLAGS,
   input [63:0] WB_RESULT_MM,

   input [2:0] WB_DR1,
   input [2:0] WB_DR2,
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
   output [1:0] WB_Final_DR3_datasize,
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
   output [31:0] WB_Final_Dcache_Address,
   output WB_Final_Dcache_Write,

   output DEP_v_wb_ld_gpr1,
   output DEP_v_wb_ld_gpr2,
   output DEP_v_wb_ld_gpr3,
   output DEP_v_wb_ld_seg,
   output DEP_v_wb_ld_mm,
   output DEP_v_wb_dcache_write,

   output wb_halt_all, 
   output wb_repne_terminate_all,
   output wb_stall,
   output wb_v_branch_taken,
   
   output [31:0] flags_dataforwarded,
   output [31:0] saved_count
   );

  //control signals
  `include "./control_store/control_store_wires.v"
  `include "./control_store/control_store_signals.v"

   //internal wires
   wire CLK_NOT; 
   //operand_select_wb
   wire [31:0] data1, saved_count; 
   //conditional_support_wb
   wire mux_not_taken_eip, wb_ld_gpr2;
   //validate_signals_wb
   wire v_wb_ld_gpr1, v_ex_ld_gpr2, v_cs_ld_gpr3, v_cs_ld_seg, v_d2_ld_mm, 
      v_ex_dcache_write, v_cs_ld_flags, v_cs_ld_eip, v_cs_ld_cs;
   //repne_halt_wb
   wire ZF; 
   //flags_wb
   wire [31:0] final_out_flags; 
   //outputs
   wire [63:0] data1_64; //64 because dcache data-in port is 64 bits incase the input is mm 
   //stall
   wire In_write_ready_not;

   inv1$ not_clk(CLK_NOT, CLK);
   operand_select_wb u_operand_select_wb(data1, WB_Final_EIP, WB_Final_CS, saved_count, CLK, PRE, CLR,
      CS_IS_CMPS_FIRST_UOP_ALL, CS_IS_CMPS_SECOND_UOP_ALL, CS_SAVE_NEIP_WB, CS_SAVE_NCS_WB,
      CS_PUSH_FLAGS_WB, CS_USE_TEMP_NEIP_WB, mux_not_taken_eip, CS_USE_TEMP_NCS_WB, WB_RESULT_A, WB_RESULT_C, WB_NEIP,
      WB_NEIP_NOT_TAKEN, WB_NCS, final_out_flags);

   conditional_support_wb u_conditional_support_wb(mux_not_taken_eip, wb_ld_gpr2, wb_branch_taken, CS_IS_JNBE_WB,  CS_IS_JNE_WB, final_out_flags, 
       CS_IS_CMOVC_WB, WB_ex_ld_gpr2_wb);

   validate_signals_wb u_validate_signals_wb(v_wb_ld_gpr1, v_ex_ld_gpr2, v_cs_ld_gpr3,
      v_cs_ld_seg, v_d2_ld_mm, v_ex_dcache_write, v_cs_ld_flags, v_cs_ld_eip, v_cs_ld_cs,
      WB_V, WB_ex_ld_gpr1_wb, wb_ld_gpr2, CS_LD_GPR3_WB, CS_LD_SEG_WB, WB_d2_ld_mm_wb, 
      WB_ex_dcache_write_wb, CS_LD_FLAGS_WB, CS_LD_EIP_WB, CS_LD_CS_WB, CS_IS_CMPS_SECOND_UOP_ALL,
      WB_d2_repne_wb, wb_repne_terminate_all);
   
   assign DEP_v_wb_ld_gpr1 = v_wb_ld_gpr1;
   assign DEP_v_wb_ld_gpr2 = v_ex_ld_gpr2;
   assign DEP_v_wb_ld_gpr3 = v_cs_ld_gpr3;
   assign DEP_v_wb_ld_seg = v_cs_ld_seg;
   assign DEP_v_wb_ld_mm = v_d2_ld_mm;
   assign DEP_v_wb_dcache_write = v_ex_dcache_write;

   repne_halt_wb u_repne_halt_wb(wb_halt_all, wb_repne_terminate_all, WB_V, CS_IS_HALT_WB, CS_IS_CMPS_SECOND_UOP_ALL,
      WB_d2_repne_wb, final_out_flags, WB_RESULT_C);

   flags_wb u_flags_wb(final_out_flags, CLK_NOT, CLR, PRE, v_cs_ld_flags, CS_POP_FLAGS_WB, 
      CS_FLAGS_AFFECTED_WB, WB_FLAGS, WB_RESULT_A);

   dr_select_wb u_dr_select_wb(WB_Final_DR1, WB_Final_DR2, CS_IS_CMPS_SECOND_UOP_ALL, 
      WB_DR1, WB_DR2, CS_DR1_D2, CS_DR2_D2);
   
   //regfile32
   assign WB_Final_DR3 = CS_DR3_WB; 
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
   assign WB_Final_ld_mm = v_d2_ld_mm; 
   //EIP register
   assign WB_Final_ld_eip = v_cs_ld_eip;
   //CS register
   assign WB_Final_ld_cs = v_cs_ld_cs;
   //Flags register
   assign WB_Final_Flags = final_out_flags;
   assign WB_Final_ld_flags = v_cs_ld_flags;
   //DCACHE outputs
   assign data1_64 = {{32{1'b0}}, data1};
   mux64_2way u_dache_data_in(WB_Final_Dcache_Data, data1_64, WB_RESULT_MM, CS_MM_MEM_WB);
   assign WB_Final_Dcache_Address = WB_ADDRESS; 
   assign WB_Final_Dcache_Write = v_ex_dcache_write;

   //stall logic
   inv1$ u_not_write_ready(In_write_ready_not, In_write_ready);
   and2$ u_wb_stall(wb_stall, v_ex_dcache_write, In_write_ready_not);
   and2$ u_wb_v_branch_taken(wb_v_branch_taken, wb_branch_taken, WB_V);
   //dataforward
   assign flags_dataforwarded = final_out_flags;

   assign WB_Final_DR3_datasize = 2'b10; 

endmodule
