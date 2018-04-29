module agen_stage2 (
   input CLK, RST, SET, V,

   // Signals to be saved in pipeline latches
   input [31:0] EIP, // for segment limit check
   input [31:0] NEIP, 
   input [15:0] NCS,
   input [127:0] CONTROL_STORE,

   input [31:0] A, B,
   input [63:0] MM_A, MM_B,
   input [31:0] SP_XCHG_DATA,
   input [31:0] ADD_BASE_DISP, ADD_SIB_SEG1,
   input [31:0] SIB_SI_DATA,
   input [15:0] SEG2_DATA,
   input [31:0] INTERRUPT_ADDR,
   input [2:0] SEG1,
			   
   input [2:0] D2_ALUK_EX,
   input [2:0] DRID1, DRID2,

   input D2_MEM_RD_ME, D2_MEM_WR_WB,
   input D2_LD_GPR1_WB, D2_LD_MM_WB,

   input [1:0] D2_DR1_SIZE_WB, D2_DR2_SIZE_WB,
   input [1:0] D2_MEM_SIZE_WB,

   // EXCEPTION/INTERRUPT STATUS
   input PAGE_FAULT_EXC_EXIST,
			   
   output [1:0] D2_DR1_SIZE_WB_OUT, D2_DR2_SIZE_WB_OUT,
   output [1:0] D2_MEM_SIZE_WB_OUT,

   // Signals for next stage latches
   output [31:0] NEIP_OUT, 
   output [15:0] NCS_OUT,
   output [127:0] CONTROL_STORE_OUT,

   output [31:0] A_OUT, B_OUT,
   output [63:0] MM_A_OUT, MM_B_OUT,
   output [31:0] SP_XCHG_DATA_OUT,
   output [31:0] MEM_RD_ADDR_OUT, MEM_WR_ADDR_OUT,

   output [2:0] D2_ALUK_EX_OUT,
   output [2:0] DRID1_OUT, DRID2_OUT,

   output D2_MEM_RD_ME_OUT, D2_MEM_WR_WB_OUT,
   output D2_LD_GPR1_WB_OUT, D2_LD_MM_WB_OUT,

   // Other signals
   output SEG_LIMIT_EXC_EXIST_OUT, PAGE_FAULT_EXC_EXIST_OUT
);
//`include "ag_control_store.v"
`include "./control_store/control_store_wires.v"
`include "./control_store/control_store_signals.v"

   assign D2_DR1_SIZE_WB_OUT = D2_DR1_SIZE_WB;
   assign D2_DR2_SIZE_WB_OUT = D2_DR2_SIZE_WB;
   assign D2_MEM_SIZE_WB_OUT = D2_MEM_SIZE_WB;

   assign NEIP_OUT = NEIP;
   assign NCS_OUT = NCS;
   assign CONTROL_STORE_OUT = CONTROL_STORE;

   assign A_OUT = A;
   assign B_OUT = B;
   assign MM_A_OUT = MM_A;
   assign MM_B_OUT = MM_B;

   assign SP_XCHG_DATA_OUT = SP_XCHG_DATA;

   wire [31:0] add_seg1_out, add_seg2_out;
   adder32_w_carry_in add_seg1 (add_seg1_out, , ADD_BASE_DISP, ADD_SIB_SEG1, 1'b0);

   // Generate SR2 address (for stack accesses)
   adder32_w_carry_in add_seg2 (add_seg2_out, , {SEG2_DATA, 16'b0}, SP_XCHG_DATA, 1'b0);
   
   // Decide MEM_RD_ADDR, MEM_WR_ADDR
   mux4_32
      mux_rd_addr (MEM_RD_ADDR_OUT, add_seg1_out, add_seg2_out, INTERRUPT_ADDR, , CS_MUX_MEM_RD_ADDR_AG[0], CS_MUX_MEM_RD_ADDR_AG[1]),
      mux_wr_addr (MEM_WR_ADDR_OUT, add_seg1_out, add_seg2_out, , , CS_MUX_MEM_WR_ADDR_AG[0], CS_MUX_MEM_WR_ADDR_AG[1]);

   assign D2_ALUK_EX_OUT = D2_ALUK_EX;
   assign DRID1_OUT = DRID1;
   assign DRID2_OUT = DRID2;

   assign D2_MEM_RD_ME_OUT = D2_MEM_RD_ME;
   assign D2_MEM_WR_WB_OUT = D2_MEM_WR_WB;
   assign D2_LD_GPR1_WB_OUT = D2_LD_GPR1_WB; 
   assign D2_LD_MM_WB_OUT = D2_LD_MM_WB;

   segment_limit_check u_seg_limit_check (
      V, D2_MEM_RD_ME, D2_MEM_WR_WB, CS_MUX_MEM_RD_ADDR_AG, CS_MUX_MEM_WR_ADDR_AG,
      SEG1, D2_MEM_SIZE_WB, ADD_BASE_DISP, SIB_SI_DATA, EIP,
      SEG_LIMIT_EXC_EXIST_OUT
   );

   assign PAGE_FAULT_EXC_EXIST_OUT = PAGE_FAULT_EXC_EXIST;
   
endmodule
