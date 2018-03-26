// Control signals from writeback stage need to be defined

module writeback (
   input CLK, SET, RST,

   input V,
   input [31:0] NEIP,
   input [15:0] NCS,
   input [63:0] CONTROL_STORE,

   input [31:0] SR1_DATA,
   input [31:0] ALU_RESULT,
   input [63:0] MM_RESULT,
   input [31:0] SP_XCHG_DATA,

   input [31:0] MEM_WR_ADDR,
   input [1:0] DATA_SIZE,

   input [1:0] DE_ALUK_EX,
   input [2:0] DRID1, DRID2,

   input D2_MEM_WR_WB, D2_LD_GPR1_WB, D2_LD_MM_WB,

   input [31:0] EFLAGS_DATA,
   input DCACHE_READY,

   output [31:0] EIP_DATA_OUT,

   output [31:0] SR1_DATA_OUT, SR2_DATA_OUT,
   output [63:0] MM_DATA_OUT,
   output [15:0] SEG_DATA_OUT, CSEG_DATA_OUT,
   output [63:0] MEM_DATA_OUT,

   output [1:0] DATA_SIZE_OUT,
   output [2:0] DRID1_OUT, DRID2_OUT,

   output V_LD_EIP, V_LD_CSEG, V_LD_GPR1, V_LD_GPR2,
   output V_LD_SEG, V_LD_MM, 

   output V_MEM_WR, WB_STALL
);
`include "../control_store/control_store_wires.v"
`include "../control_store/control_store_signals.v"

   wire [31:0] mux_sr1_data_out, mux_mem_out;
   wire and_sz_64_out;

   assign EIP_DATA_OUT = NEIP;

   mux4$ mux_sr1_data [31:0] (mux_sr1_data_out, ALU_RESULT, SR1_DATA, NEIP, EFLAGS_DATA, CS_MUX_SR1_MEM_DATA_WB[0], CS_MUX_SR1_MEM_DATA_WB[1]);
   assign SR1_DATA_OUT = mux_sr1_data_out;
   assign SR2_DATA_OUT = SP_XCHG_DATA;
   assign MM_DATA_OUT = MM_RESULT;
   assign SEG_DATA_OUT = mux_sr1_data_out[15:0];
   assign CSEG_DATA_OUT = NCS;

   and2$ and_sz_64 (and_sz_64_out, DATA_SIZE[0], DATA_SIZE[1]);
   mux2$ mux_mem [31:0] (mux_mem_out, mux_sr1_data_out, MM_RESULT[31:0], and_sz_64_out);
   assign MEM_DATA_OUT = {MM_RESULT[63:32], mux_mem_out};
   assign DATA_SIZE_OUT = DATA_SIZE;

   assign DRID1_OUT = DRID1; // To GPRs, SEGRs, MMX registers
   assign DRID2_OUT = DRID2; // to GPRs only

   and2$
      and_v_ld_eip (V_LD_EIP, V, CS_LD_EIP_WB),
      and_v_ld_cseg (V_LD_CSEG, V, CS_LD_CSEG_WB),
      and_v_ld_gpr1 (V_LD_GPR1, V, D2_LD_GPR1_WB),
      and_v_ld_gpr2 (V_LD_GPR2, V, CS_LD_GPR2_WB),
      and_v_ld_mm (V_LD_MM, V, D2_LD_MM_WB),
      and_v_ld_seg (V_LD_SEG, V, CS_LD_SEG_WB),
      and_v_mem_wr (V_MEM_WR, V, D2_MEM_WR_WB);
endmodule
