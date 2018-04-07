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
   input CLK, SET, RST, //not uesd SET/RST

   input WB_V,
   input [31:0] WB_NEIP,
   input [15:0] WB_NCS,
   input [63:0] WB_CONTROL_STORE,
   //pseudo-control store signals not from control store but generated in decode
   input [1:0] de_datasize_all,
   input [2:0] de_aluk_ex, 
   input de_mem_wr_wb, 
   input de_ld_gpr1_wb,
   input de_dcache_write_wb, 
   input [6:0] de_flags_affected_wb,

   input [31:0] WB_ALU32_RESULTS,
   input [31:0] WB_COUNT, 
   input [63:0] WB_MM_A, WB_MM_B,

   input [31:0] WB_ADDRESS,

   input [2:0] WB_DR1, WB_DR2, WB_DR3,

   output [2:0] Out_DR1, Out_DR2, Out_DR3,
   output [31:0] Out_DR1_Data, Out_DR2_Data, Out_DR3_Data, 
   output out_v_de_ld_gpr1_wb, out_v_cs_ld_gpr2_wb, out_v_cs_ld_gpr3_wb,
   output [1:0] out_de_datasize,
   output [31:0] Out_Dcache_Data, Out_Dcache_Address
);

   //control store
   wire cs_is_cmps_first_uop_all; 
   wire cs_is_cmps_second_uop_all; 
   wire cs_is_first_of_repne_wb; 
   wire cs_ld_gpr2_wb; 
   wire cs_ld_gpr3_wb; 
   wire cs_ld_flags_wb; 

   //internal wires for each box output in schematic
      //
   wire [31:0] cmps_updated_pointer, cmps_first_pointer;
   wire [31:0] internal_count;
   wire ex_repne_termination_all;
      //validate writeback signals for GPR and DCACHE
   wire v_de_ld_gpr1_wb, v_cs_ld_gpr2_wb, v_cs_ld_gpr3_wb, v_de_dache_write_wb, v_cs_ld_flags_wb;
      //internal data
   wire [31:0] current_flags; 
   wire data1, data2, data3; 

   undo_control_store u_undo_control_store(
      cs_is_cmps_first_uop_all, //0
      cs_is_cmps_second_uop_all, //1
      cs_is_first_of_repne_wb, //2
      cs_ld_gpr2_wb, //3
      cs_ld_gpr3_wb, //4
      cs_ld_flags_wb,
      EX_CONTROL_STORE
   );

   CMPS_POINTER_LOGIC (cmps_updated_pointer, WB_CMPS_POINTER, de_datasize_all, current_flags[11]); 
   
   reg32e$ cmps_temp_pointer (CLK, cmps_updated_pointer, cmps_first_pointer, , 1'b1, 1'b1, cs_is_cmps_first_uop_all);
   
   Flags_WB(current_flags, CLK, v_cs_ld_flags_wb, de_flags_affected_wb, WB_FLAGS);

   Repne_Count_Logic u_Repne_Count_Logic(internal_count, WB_COUNT, cs_is_first_of_repne_wb, cs_is_cmps_second_uop_all, current_flags[6], CLK);

   and2$ u_validate_gpr1(v_de_ld_gpr1_wb, WB_V, de_ld_gpr1_wb);
   and2$ u_validate_gpr2(v_cs_ld_gpr2_wb, WB_V, cs_ld_gpr2_wb);
   and2$ u_validate_gpr3(v_cs_ld_gpr3_wb, WB_V, cs_ld_gpr3_wb);
   and2$ u_validate_mem_writes(v_de_dache_write_wb, WB_V, de_dcache_write_wb);
   and2$ u_validate_flag_writes(v_cs_ld_flags_wb, WB_V, cs_ld_flags_wb);

   //Desination Select_WB

   mux32_2way u_mux_d1(data1, WB_ALU32_RESULTS, cmps_first_pointer, cs_is_cmps_first_uop_all);
   assign data2 = cmps_updated_pointer;
   assign data3 = internal_count; 

   //REG_FILE32 outputs
   assign Out_DR1 = WB_DR1;
   assign Out_DR2 = WB_DR2;
   assign Out_DR3 = WB_DR3; 
   assign Out_DR1_data = data1;
   assign Out_DR2_data = data2;
   assign Out_DR3_data = data3;
   assign out_v_de_ld_gpr1_wb = v_de_ld_gpr1_wb; 
   assign out_v_cs_ld_gpr2_wb = v_cs_ld_gpr2_wb;
   assign out_v_de_ld_gpr3_wb = v_cs_ld_gpr3_wb; 

   //DCACHE outputs
   assign out_de_datasize = de_datasize_all;
   assign Out_Dcache_Data = data1; 
   assign Out_Dcache_Address = WB_ADDRESS; 

endmodule
