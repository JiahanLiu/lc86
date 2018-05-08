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
   input [15:0] SEG1_DATA,
   input [15:0] SEG2_DATA,
   input [31:0] INTERRUPT_ADDR,
   input [2:0] SEG1,
			   
   input [2:0] D2_ALUK_EX,
   input [2:0] DRID1, DRID2,

   input D2_MEM_RD_ME, D2_MEM_WR_WB,
   input D2_LD_GPR1_WB, D2_LD_MM_WB,

   input [1:0] D2_DR1_SIZE_WB, D2_DR2_SIZE_WB,
   input [1:0] D2_MEM_SIZE_WB,
   input D2_REPNE_WB, EFLAGS_DF,

   // EXCEPTION/INTERRUPT STATUS
   input PAGE_FAULT_EXC_EXIST, EXC_EN_V,
			   
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
   output SEG_LIMIT_EXC_EXIST_OUT, PAGE_FAULT_EXC_EXIST_OUT, AG_REPNE_WB,
   output JMP_STALL_OUT, V_LD_DF_OUT
);
//`include "ag_control_store.v"
`include "../pipeline/control_store/control_store_wires.v"
`include "../pipeline/control_store/control_store_signals.v"

   assign D2_DR1_SIZE_WB_OUT = D2_DR1_SIZE_WB;
   assign D2_DR2_SIZE_WB_OUT = D2_DR2_SIZE_WB;
   assign D2_MEM_SIZE_WB_OUT = D2_MEM_SIZE_WB;

   assign NEIP_OUT = NEIP;
   assign NCS_OUT = NCS;
   assign CONTROL_STORE_OUT = CONTROL_STORE;

   wire [31:0] mux_repne_base_out;
   
   mux2_32 mux_a_out (A_OUT, A, mux_repne_base_out, D2_REPNE_WB);
   // assign A_OUT = A;

   wire [31:0] mux_b_out;
   mux2_32 mux_b (mux_b_out, B, 32'b1, CS_MUX_IMM1_AG);
   assign B_OUT = mux_b_out;

   assign MM_A_OUT = MM_A;
   assign MM_B_OUT = MM_B;

   assign AG_REPNE_WB = D2_REPNE_WB;

   assign SP_XCHG_DATA_OUT = SP_XCHG_DATA;

   wire [31:0] add_seg1_out, add_seg2_out;
   adder32_w_carry_in add_seg1 (add_seg1_out, , ADD_BASE_DISP, ADD_SIB_SEG1, 1'b0);

   // Generate SR2 address (for stack accesses)
   adder32_w_carry_in add_seg2 (add_seg2_out, , {SEG2_DATA, 16'b0}, SP_XCHG_DATA, 1'b0);

   wire [3:0] mux_neg_size_out, mux_pos_size_out;
   wire [31:0] mux_cmps_size_out;

   // REPNE CMPS logic
   wire [31:0] add_cmps_seg1_out;
   adder32_w_carry_in add_cmps_seg1 (add_cmps_seg1_out, , A, {SEG1_DATA, 16'b0}, 1'b0);

   mux4_4 mux_neg_size (mux_neg_size_out, 4'b1111, 4'b1110, 4'b1100, , D2_MEM_SIZE_WB[0], D2_MEM_SIZE_WB[1]);
   mux4_4 mux_pos_size (mux_pos_size_out, 4'b0001, 4'b0010, 4'b0100, , D2_MEM_SIZE_WB[0], D2_MEM_SIZE_WB[1]);
   mux2_32 mux_cmps_size (mux_cmps_size_out, {28'b0, mux_pos_size_out}, {28'hFFF_FFFF, mux_neg_size_out}, EFLAGS_DF);

   wire [31:0] Qcmps_esi_addr, Qcmps_edi_addr;
   wire [31:0] add_esi_addr_out, add_edi_addr_out, mux_cmps_save_esi_addr_out, mux_cmps_save_edi_addr_out;
   wire [31:0] mux_cmps_rd_addr_out;

   adder32_w_carry_in add_esi_addr (add_esi_addr_out, , Qcmps_esi_addr, mux_cmps_size_out, 1'b0);
   adder32_w_carry_in add_edi_addr (add_edi_addr_out, , Qcmps_edi_addr, mux_cmps_size_out, 1'b0);
   mux2_32 mux_cmps_save_esi_addr (mux_cmps_save_esi_addr_out, add_cmps_seg1_out, add_esi_addr_out, CS_REPNE_STEADY_STATE);
   mux2_32 mux_cmps_save_edi_addr (mux_cmps_save_edi_addr_out, add_cmps_seg1_out, add_edi_addr_out, CS_REPNE_STEADY_STATE);

   reg32e$ reg_cmps_save_esi_addr (CLK, mux_cmps_save_esi_addr_out, Qcmps_esi_addr, , RST, SET, CS_IS_CMPS_FIRST_UOP_ALL);
   reg32e$ reg_cmps_save_edi_addr (CLK, mux_cmps_save_edi_addr_out, Qcmps_edi_addr, , RST, SET, CS_IS_CMPS_SECOND_UOP_ALL);
 
   mux2_32 mux_cmps_rd_addr (mux_cmps_rd_addr_out, mux_cmps_save_esi_addr_out, mux_cmps_save_edi_addr_out, CS_IS_CMPS_SECOND_UOP_ALL);

   // Decide MEM_RD_ADDR, MEM_WR_ADDR
   mux4_32
      mux_rd_addr (MEM_RD_ADDR_OUT, add_seg1_out, add_seg2_out, INTERRUPT_ADDR, mux_cmps_rd_addr_out, CS_MUX_MEM_RD_ADDR_AG[0], CS_MUX_MEM_RD_ADDR_AG[1]),
      mux_wr_addr (MEM_WR_ADDR_OUT, add_seg1_out, add_seg2_out, , , CS_MUX_MEM_WR_ADDR_AG[0], CS_MUX_MEM_WR_ADDR_AG[1]);

   assign D2_ALUK_EX_OUT = D2_ALUK_EX;
   assign DRID1_OUT = DRID1;
   assign DRID2_OUT = DRID2;

   assign D2_MEM_RD_ME_OUT = D2_MEM_RD_ME;
   assign D2_MEM_WR_WB_OUT = D2_MEM_WR_WB;
   assign D2_LD_GPR1_WB_OUT = D2_LD_GPR1_WB; 
   assign D2_LD_MM_WB_OUT = D2_LD_MM_WB;

   wire [31:0] add_a_out, add_next_esi_out, add_next_edi_out,
               mux_esi_out, mux_edi_out;
   wire [31:0] Qcmps_esi, Qcmps_edi;
   wire [31:0] Qcmps_src1_seg, Qcmps_src2_seg;

   wire [31:0] mux_cmps_base_out;
   wire [2:0] mux_cmps_seg_out, mux_repne_seg_out;

   wire [2:0] cmps_src1_seg, cmps_src2_seg;

   assign cmps_src1_seg = Qcmps_src1_seg[2:0];
   assign cmps_src2_seg = Qcmps_src2_seg[2:0];

//   wire [3:0] mux_a_size_out;
//   mux4_4 mux_a_size (mux_a_size_out, 4'b0000, 4'b0001, 4'b0011, , D2_MEM_SIZE_WB[0], D2_MEM_SIZE_WB[1]);
   
//   adder32_w_carry_in add_a (add_a_out, , A, {28'b0, mux_a_size_out}, 1'b0);
   adder32_w_carry_in add_a (add_a_out, , A, mux_cmps_size_out, 1'b0);

   adder32_w_carry_in add_next_esi (add_next_esi_out, , Qcmps_esi, mux_cmps_size_out, 1'b0);
   adder32_w_carry_in add_edi (add_next_edi_out, , Qcmps_edi, mux_cmps_size_out, 1'b0);

   mux2_32 mux_esi (mux_esi_out, add_a_out, add_next_esi_out, CS_REPNE_STEADY_STATE);
   mux2_32 mux_edi (mux_edi_out, add_a_out, add_next_edi_out, CS_REPNE_STEADY_STATE);

   reg32e$ reg_save_esi (CLK, mux_esi_out, Qcmps_esi, , RST, SET, CS_IS_CMPS_FIRST_UOP_ALL);
   reg32e$ reg_save_src1_segid (CLK, {29'b0, SEG1}, Qcmps_src1_seg, , RST, SET, CS_IS_CMPS_FIRST_UOP_ALL);
   reg32e$ reg_save_edi (CLK, mux_edi_out, Qcmps_edi, , RST, SET, CS_IS_CMPS_SECOND_UOP_ALL);
   reg32e$ reg_save_src2_segid (CLK, {29'b0, SEG1}, Qcmps_src2_seg, , RST, SET, CS_IS_CMPS_SECOND_UOP_ALL);

   mux2_32 mux_cmps_base (mux_cmps_base_out, Qcmps_esi, Qcmps_edi, CS_IS_CMPS_SECOND_UOP_ALL);
   mux2_3 mux_cmps_seg (mux_cmps_seg_out, cmps_src1_seg, cmps_src2_seg, CS_IS_CMPS_SECOND_UOP_ALL);
   
   mux2_32 mux_repne_base (mux_repne_base_out, A, mux_cmps_base_out, CS_REPNE_STEADY_STATE);
   mux2_3 mux_repne_seg (mux_repne_seg_out, SEG1, mux_cmps_seg_out, CS_REPNE_STEADY_STATE);

//   wire seg_limit_v_in;
//   inv1$ inv_exc_en_v (exc_en_v_bar, EXC_EN_V);
//   and2$ and_seg_limit_v_in(seg_limit_v_in, V, exc_en_v_bar);

   segment_limit_check u_seg_limit_check (
      V, D2_MEM_RD_ME, D2_MEM_WR_WB, CS_MUX_MEM_RD_ADDR_AG, CS_MUX_MEM_WR_ADDR_AG,
      SEG1, D2_MEM_SIZE_WB, ADD_BASE_DISP, SIB_SI_DATA, EIP,
      D2_REPNE_WB, mux_repne_base_out, mux_repne_seg_out,

      SEG_LIMIT_EXC_EXIST_OUT
   );

   assign PAGE_FAULT_EXC_EXIST_OUT = PAGE_FAULT_EXC_EXIST;

   wire or_jmp_stall_out;
   or3$ or_jmp_stall (or_jmp_stall_out, CS_JMP_STALL_DE, CS_IS_NEAR_RET_M2, CS_IS_FAR_RET_M2);
   and2$ and_jmp_stall (JMP_STALL_OUT, V, or_jmp_stall_out);

   and3$ and_ld_df (V_LD_DF_OUT, V, CS_LD_FLAGS_WB, CS_FLAGS_AFFECTED_WB[5]);
   
endmodule
