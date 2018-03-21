	   
module address_generation (
   input CLK, SET, RST,

   // Signals to be saved in pipeline latches
   input [31:0] EIP, 
   input [15:0] CS,
   input [63:0] CONTROL_STORE,

   input [1:0] D2_DATA_SIZE_AG,
   input D2_SR1_NEEDED_AG, D2_SEG1_NEEDED_AG, D2_MM1_NEEDED_AG,

   input D2_MEM_RD_ME, D2_MEM_WR_ME,
   input [2:0] D2_ALUK_EX,
   input D2_LD_GPR1_WB, D2_LD_MM_WB,

   input [2:0] SR1, SR2, SEG1, SEG2,
   input [31:0] IMM32, DISP32,

   input DE_SIB_EN_AG, DE_DISP_EN_AG, DE_BASE_REG_EN_AG,
   input DE_MUX_SEG_AG, DE_CMPXCHG_AG,
   input [1:0] DE_SIB_S_AG,

   input [31:0] SR1_DATA, SR2_DATA, SR3_DATA, SIB_I_DATA,
   input [15:0] SEG1_DATA, SEG2_DATA,
   input [63:0] MM1_DATA, MM2_DATA,

   // Signals to register file
   output [2:0] SR1_OUT, SR2_OUT, SEG1_OUT, SEG2_OUT,
   output [1:0] DATA_SIZE_OUT,

   // Signals for next stage latches
   output [31:0] NEIP_OUT, 
   output [16:0] NCS_OUT,
   output [63:0] CONTROL_STORE_OUT,

   output [31:0] A_OUT, B_OUT,
   output [63:0] MM_A_OUT, MM_B_OUT,
   output [31:0] IMM32_OUT, SP_XCHG_DATA_OUT,
   output [31:0] MEM_RD_ADDR_OUT, MEM_WR_ADDR_OUT,

   output [2:0] DE_ALUK_EX_OUT,
   output [2:0] DRID1_OUT, DRID2_OUT,

   output D2_LD_GPR1_WB_OUT, D2_LD_MM_WB_OUT,

   // Other signals
   output DEP_STALL_OUT, SEG_LIMIT_EXC_OUT
);
`include "ag_control_store.v"

   wire [31:0] mux_disp_out, mux_base_reg_out, add_base_disp_out;
   wire [31:0] shf_sib_idx_out, mux_sib_si_out, add_sib_out;
   wire [15:0] mux_seg1_out;
   wire [31:0] add_seg1_out;

   wire [1:0] mux_push_size_out;
   wire [31:0] mux_push_add_out, add_sp_out, add_seg2_out;

   assign SR1_OUT = SR1;
   assign SR2_OUT = SR2;
   assign SEG1_OUT = SEG1;
   assign SEG2_OUT = SEG2;
   assign DATA_SIZE_OUT = DATA_SIZE;

   mux4_1$
      mux_a [31:0] (A_OUT, SR1_DATA, SEG1_DATA, SEG2_DATA, {16'b0, CS}, CS_MUX_A_AG);

   assign B_OUT = SR2_DATA;
   assign MM_A_OUT = MM1_DATA;
   assign MM_B_OUT = MM2_DATA;
   assign IMM32_OUT = IMM32;

   // Generate SR1 address
   mux2_1$
      mux_disp [31:0] (mux_disp_out, 32'b0, DISP32, DE_DISP_EN_AG),
      mux_base_reg [31:0] (mux_base_reg_out, 32'b0, SR1_DATA, DE_BASE_REG_EN_AG);
   adder32 add_base_disp (add_base_disp_out, , mux_disp_out, mux_base_reg_out); 

   sal32 shf_sib_idx (shf_sib_idx_out, SIB_I_DATA, {3'b0, DE_SIB_S_AG});
   mux2_1$ mux_sib_si [31:0] (mux_sib_si_out, 32'b0, shf_sib_idx_out, DE_SIB_EN_AG);
   adder32 add_sib (add_sib_out, , add_base_disp_out, mux_sib_si_out);

   mux2_1$ mux_seg1 [15:0] (mux_seg1_out, SEG1_DATA, CS, DE_MUX_SEG_AG);
   adder32 add_seg1 (add_seg1_out, , add_sib_out, {mux_seg1_out, 16'b0});

   // Generate SR2 address (for stack accesses)
   mux2_1$
      mux_push_size [1:0] (mux_push_size_out, 2'b10, 2'b00, DATA_SIZE[1]), // select to add -2 or -4 on data size
      mux_push_add [31:0] (mux_push_add_out, 32'b0, {29'b1, mux_push_size_out}, DE_PUSH_INST_AG);
   adder32 
      add_sp (add_sp_out, , SR2_DATA, mux_push_add_out),
      add_seg2 (add_seg2_out, , {SEG2_DATA, 16'b0}, add_sp_out);
  
   mux2_1$
      mux_rd_addr [31:0] (MEM_RD_ADDR_OUT, add_seg1_out, add_seg2_out, CS_MUX_RD_ADDR_AG),
      mux_wr_addr [31:0] (MEM_WR_ADDR_OUT, add_seg1_out, add_seg2_out, CS_MUX_WR_ADDR_AG);

   mux2_1$
      mux_sp_xchg [31:0] (SP_XCHG_DATA_OUT, mux_push_add_out, SR3_DATA, DE_CMPXCHG_AG);
   
   mux2_1$
      mux_drid1 [2:0] (DRID1_OUT, SR1, SR2, CS_MUX_DRID1_AG);

   assign DRID2_OUT = SR2;

   assign D2_MEM_RD_ME_OUT = D2_MEM_RD_ME;
   assign D2_MEM_WR_ME_OUT = D2_MEM_WR_ME;
   assign D2_ALUK_EX_OUT = D2_ALUK_EX;
   assign D2_LD_GPR1_WB_OUT = D2_LD_GPR1_WB; 
   assign D2_LD_MM_WB_OUT = D2_LD_MM_WB;
   
endmodule

