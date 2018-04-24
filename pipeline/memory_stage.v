module memory_stage (
   input CLK, RST, SET, V,

   input [31:0] NEIP,
   input [15:0] NCS,
   input [127:0] CONTROL_STORE,

   input [31:0] A, B,
   input [63:0] MM_A, MM_B,
   input [31:0] SP_XCHG_DATA,

   input [31:0] MEM_RD_ADDR, MEM_WR_ADDR,
   input [1:0] D2_DR1_SIZE_WB, D2_DR2_SIZE_WB,
   input [1:0] D2_MEM_SIZE_WB,

   input [2:0] DE_ALUK_EX,
   input [2:0] DRID1, DRID2,

   input D2_MEM_RD_ME, D2_MEM_WR_WB, D2_LD_GPR1_WB, D2_LD_MM_WB,

   input [63:0] DCACHE_DATA,
   input DCACHE_READY,

   output DCACHE_EN,

   output [31:0] NEIP_OUT,
   output [15:0] NCS_OUT,
   output [127:0] CONTROL_STORE_OUT,

   output [31:0] A_OUT, B_OUT,
   output [63:0] MM_A_OUT, MM_B_OUT,
   output [31:0] SP_XCHG_DATA_OUT,

   output [31:0] MEM_RD_ADDR_OUT, MEM_WR_ADDR_OUT,
   output [1:0] D2_DR1_SIZE_WB_OUT, D2_DR2_SIZE_WB_OUT,
   output [1:0] D2_MEM_SIZE_WB_OUT,

   output [2:0] DE_ALUK_EX_OUT,
   output [2:0] DRID1_OUT, DRID2_OUT,

   output D2_MEM_WR_WB_OUT, D2_LD_GPR1_WB_OUT, D2_LD_MM_WB_OUT
);
`include "./control_store/control_store_wires.v"
`include "./control_store/control_store_signals.v"

   wire [31:0] mux_imm_out;

   // PLACEHOLDER FOR DEBUG - TODO
   assign DCACHE_DATA = 63'h12; 

   assign NEIP_OUT = NEIP;
   assign NCS_OUT = NCS;
   assign CONTROL_STORE_OUT = CONTROL_STORE;

   mux2$
      mux_a [31:0] (A_OUT, A, DCACHE_DATA[31:0], D2_MEM_RD_ME),
      mux_b [31:0] (B_OUT, B, A, CS_MUX_B_ME),
      mux_mm_a [63:0] (MM_A_OUT, MM_A, DCACHE_DATA, D2_MEM_RD_ME);

   assign MM_B_OUT = MM_B;

   mux2$
      mux_imm [31:0] (mux_imm_out, 32'b0, B, CS_MUX_IMM_ADD_ME);
   adder32_w_carry_in
      add_xchg (SP_XCHG_DATA_OUT, , mux_imm_out, SP_XCHG_DATA, 1'b0);

   assign MEM_RD_ADDR_OUT = MEM_RD_ADDR; // TODO: implement TLB lookup
   assign MEM_WR_ADDR_OUT = MEM_WR_ADDR;
   assign D2_DR1_SIZE_WB_OUT = D2_DR1_SIZE_WB;
   assign D2_DR2_SIZE_WB_OUT = D2_DR2_SIZE_WB;
   assign D2_MEM_SIZE_WB_OUT = D2_MEM_SIZE_WB;

   assign DE_ALUK_EX_OUT = DE_ALUK_EX;
   assign DRID1_OUT = DRID1;
   assign DRID2_OUT = DRID2;

   assign D2_MEM_WR_WB_OUT = D2_MEM_WR_WB;
   assign D2_LD_GPR1_WB_OUT = D2_LD_GPR1_WB;
   assign D2_LD_MM_WB_OUT = D2_LD_MM_WB;

endmodule
