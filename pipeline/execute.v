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
   
   //need nelson to make these signals
  wire CS_IS_CMPS_FIRST_UOP_ALL;
  wire CS_IS_CMPS_SECOND_UOP_ALL; 
  wire CS_IS_FIRST_OF_REPNE_WB; 
  assign CS_IS_CMPS_FIRST_UOP_ALL = 0;
  assign CS_IS_CMPS_SECOND_UOP_ALL = 0; 
  assign CS_IS_FIRST_OF_REPNE_WB = 0; 

  //control signals
  `include "../control_store/control_store_wires.v"
  `include "../control_store/control_store_signals.v"

  //internal wires
  wire [31:0] a, b;
  wire [31:0] cmps_first_mem;

   //Operand_Select_EX
   assign a = EX_A;
   mux32_2way u_select_b(b, EX_B, cmps_first_mem, CS_IS_CMPS_SECOND_UOP_ALL); 
   
   //String_Support
   reg32e$ u_cmps_temp_mem (CLK, EX_A, cmps_first_mem, , 1'b1, 1'b1, CS_IS_CMPS_FIRST_UOP_ALL);
   assign WB_CMPS_POINTER_next = EX_B; 
   assign WB_COUNT_next = EX_COUNT; 

   //ALU32
   alu32 u_alu32(WB_ALU32_RESULT_next, WB_FLAGS_next, a, b, EX_de_aluk_ex);

   //EX latches pass to WB latches
  assign WB_V_next = EX_V;
  assign WB_NEIP_next = EX_NEIP; 
  assign WB_NCS_next = EX_NCS; 
  assign WB_CONTROL_STORE_next = EX_CONTROL_STORE;
  assign WB_de_datasize_all_next = EX_de_datasize_all;
  assign WB_de_aluk_ex_next = EX_de_aluk_ex;
  assign WB_de_ld_gpr1_wb_next = EX_de_ld_gpr1_wb;
  assign WB_de_dcache_write_wb_next = EX_de_dcache_write_wb;
  assign WB_de_flags_affected_wb_next = EX_de_flags_affected_wb;

  assign WB_DR1_next = EX_DR1;
  assign WB_DR2_next = EX_DR2;
  assign WB_DR3_next = EX_DR3; 

endmodule
