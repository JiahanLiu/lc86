// Control store width needs to be adjusted

module execute (
   input CLK, SET, RST, //not uesd SET/RST

   input EX_V,
   input [31:0] EX_NEIP,
   input [15:0] EX_NCS,
   input [63:0] EX_CONTROL_STORE,
   //pseudo-control store signals not from control store but generated in decode
   input [1:0] EX_de_datasize_all,
   input [2:0] EX_de_aluk_ex, 
   input EX_de_mem_wr_wb, 
   input EX_de_ld_gpr1_wb,
   input EX_de_dcache_write_wb, 
   input [6:0] EX_de_flags_affected_wb,

   input [31:0] EX_A, EX_B,
   input [31:0] EX_COUNT, 
   input [63:0] EX_MM_A, EX_MM_B,

   input [31:0] EX_ADDRESS,

   input [2:0] EX_DR1, EX_DR2, EX_DR3,

   output WB_V_next,
   output [31:0] WB_NEIP_next, 
   output [15:0] WB_NCS_next,
   output [63:0] WB_CONTROL_STORE_next,

   output [1:0] WB_de_datasize_all_next,
   output [2:0] WB_de_aluk_ex_next,
   output WB_de_ld_gpr1_wb_next,
   output WB_de_dcache_write_wb_next, 
   output [6:0] WB_de_flags_affected_wb_next,

   output [31:0] WB_ALU32_RESULT_next,
   output [31:0] WB_FLAGS_next,
   output [31:0] WB_CMPS_POINTER_next,
   output [31:0] WB_COUNT_next, 

   output [2:0] WB_DR1_next, WB_DR2_next, WB_DR3_next
);
   
   //control store
  wire cs_is_cmps_first_uop_all;
  wire cs_is_cmps_second_uop_all; 
  wire cs_is_first_of_repne_wb; 
  wire cs_ld_gpr2_wb; 
  wire cs_ld_gpr3_wb; 
  wire cs_ld_flags_wb; 

  //internal wires
  wire [31:0] a, b;
  wire [31:0] cmps_first_mem;


  undo_control_store u_undo_control_store(
    cs_is_cmps_first_uop_all, 
    cs_is_cmps_second_uop_all, 
    cs_is_first_of_repne_wb, 
    cs_ld_gpr2_wb, 
    cs_ld_gpr3_wb, 
    cs_ld_flags_wb, 
    EX_CONTROL_STORE
  );

   //Operand_Select_EX
   assign a = EX_A;
   mux32_2way u_select_b(b, EX_B, cmps_first_mem, cs_is_cmps_second_uop_all); 
   
   //String_Support
   reg32e$ u_cmps_temp_mem (CLK, EX_A, cmps_first_mem, , 1'b1, 1'b1, cs_is_cmps_first_uop_all);
   assign WB_CMPS_POINTER_next = EX_B; 
   assign WB_COUNT_next = EX_COUNT; 

   //ALU32
   alu32 u_alu32(WB_ALU32_RESULT_next, WB_FLAGS_next, a, b, de_aluk_ex);



endmodule
