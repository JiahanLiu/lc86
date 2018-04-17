//Flags is a 32 bit register. Here each flag's location within the register:
/*
assign flags[11] = OF; 
assign flags[10] = DF; 

assign flags[7] = SF; 
assign flags[6] = ZF; 

assign flags[4] = AF; 
assign flags[2] = PF; 
assign flags[0] = CF; 
*/
module writeback (
   input CLK, PRE, CLR, //not used SET/RST

   input WB_V,
   input [31:0] WB_NEIP,
   input [15:0] WB_NCS,
   input [127:0] CONTROL_STORE,
   //pseudo-control store signals not from control store but generated in decode
   input [1:0] WB_de_datasize_all,
   input WB_ex_ld_gpr1_wb,
   input WB_ex_ld_gpr2_wb,
   input WB_ex_dcache_write_wb,
   input WB_de_repne_wb, 

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
   output CF_dataforwarded,
   output AF_dataforwarded
   );

  //control signals
  `include "./control_store/control_store_wires.v"
  `include "./control_store/control_store_signals.v"

   //internal wires
   //operand_select_wb
   wire [31:0] data1; 
   //conditional_support_wb
   wire wb_ld_eip, wb_ld_gpr1;
   //validate_signals_wb
   wire v_wb_ld_gpr1, v_ex_ld_gpr2, v_cs_ld_gpr3, v_cs_ld_seg, v_cs_ld_mm, v_ex_dcache_write, v_cs_ld_flags, v_wb_ld_eip;
   //repne_halt_wb
   wire ZF; 
   //flags_wb
   wire [31:0] current_flags;
   wire v_cs_ld_flags_wb; 
   //outputs
   wire [63:0] data1_64; //64 because dcache data-in port is 64 bits incase the input is mm 
   //stall
   wire In_write_ready_not;

   operand_select_wb u_operand_select_wb(data1, CLK, CS_IS_CMPS_FIRST_UOP_ALL, CS_IS_CMPS_SECOND_UOP_ALL, WB_RESULT_A);
   conditional_support_wb u_conditional_support_wb(wb_ld_eip, wb_ld_gpr1, CS_IS_JNBE_WB, CS_IS_JNE_WB, CS_LD_EIP_WB, CF, ZF, CS_IS_CMOVC_WB, WB_ex_ld_gpr1_wb);
   validate_signals_wb u_validate_signals_wb(v_wb_ld_gpr1, v_ex_ld_gpr2, v_cs_ld_gpr3, v_cs_ld_seg, v_cs_ld_mm, v_ex_dcache_write, v_cs_ld_flags, v_wb_ld_eip,
      WB_V, wb_ld_gpr1, WB_ex_ld_gpr2_wb, CS_LD_GPR3_WB, CS_LD_SEG_WB, CS_LD_MM_WB, WB_ex_dcache_write_wb, CS_LD_FLAGS_WB, wb_ld_eip);
   assign DEP_v_wb_ld_gpr1 = v_wb_ld_gpr1;
   assign DEP_v_wb_ld_gpr2 = v_ex_ld_gpr2;
   assign DEP_v_wb_ld_gpr3 = v_cs_ld_gpr3;
   assign DEP_v_wb_ld_seg = v_cs_ld_seg;
   assign DEP_v_wb_ld_mm = v_cs_ld_mm;
   assign DEP_v_wb_dcache_write = v_ex_dcache_write;

   repne_halt_wb u_repne_halt_wb(wb_halt_all, wb_repne_terminate_all, WB_V, CS_IS_HALT_WB, CS_IS_CMPS_SECOND_UOP_ALL, WB_de_repne_wb, ZF, WB_RESULT_C);
   flags_wb u_flags_wb(current_flags, CLK, v_cs_ld_flags_wb, CS_FLAGS_AFFECTED_WB, WB_FLAGS);
   assign ZF = current_flags[6];
   assign CF = current_flags[0];

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
   //segfile
   assign WB_Final_ld_seg = v_cs_ld_seg; 
   //regfile64
   assign WB_Final_MM_Data = WB_RESULT_MM; 
   assign WB_Final_ld_mm = v_cs_ld_mm; 
   //EIP register
   assign WB_Final_EIP = WB_NEIP; 
   assign WB_Final_ld_eip = v_wb_ld_eip;
   //DCACHE outputs
   assign data1_64 = {{32{1'b0}}, data1};
   mux64_2way u_dache_data_in(WB_Final_Dcache_Data, data1_64, WB_RESULT_MM, CS_MM_OPERATION);
   assign WB_Final_Dcache_Data = data1; 
   assign WB_Final_Dcache_Address = WB_ADDRESS; 

   //stall logic
   inv1$ u_not_write_ready(In_write_ready_not, In_write_ready);
   and2$ u_wb_stall(WB_stall, v_ex_dcache_write, In_write_ready_not);

   //dataforward
   assign CF_dataforwarded = current_flags[0];
   assign AF_dataforwarded = current_flags[4];
endmodule
