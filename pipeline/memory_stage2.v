module memory_stage2 (
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

   output D2_MEM_WR_WB_OUT, D2_LD_GPR1_WB_OUT, D2_LD_MM_WB_OUT,
   output JMP_STALL_OUT, V_LD_DF_OUT
);
`include "../pipeline/control_store/control_store_wires.v"
`include "../pipeline/control_store/control_store_signals.v"

   wire [15:0] mux_imm_out;
   wire [63:0] buf_mem_out;

   bufferH64$ buf_mem [63:0] (buf_mem_out, DCACHE_DATA);

// for near return
// if data size is 32, EIP = MEM[31:0] --also JMP r/m, CALL r/m
// if data size is 16, EIP = {16'b0, MEM[15:0]}
// for far return
// if data size is 64, EIP = MEM[31:0]; CS = MEM[47:32] --also IRETD
// if data size is 32, EIP = {16'b0, MEM[15:0]}; CS = MEM[31:16]
// for loading from IDT
// data size 64 EIP = {MEM[63:48], MEM[15:0}, CS = MEM[31:16]
//
// EIP[31:16] = MEM[31:16] -- near ret (32), JMP MOD_EQ_MEM, CALL MOD_EQ_MEM, far ret (64), IRETD
// EIP[31:16] = MEM[63:48] -- IDT LOAD
// EIP[31:16] = A[31:16]   -- JMP MOD_EQ_REG, CALL MOD_EQ_REG
// EIP[31:16] = 16'b0      -- near ret (16), far ret (32)
//
// EIP[15:0] = A[15:0]    -- JMP MOD_EQ_REG, CALL MOD_EQ_REG
// EIP[15:0] = MEM[15:0]  -- near ret all, far ret all, JMP r/m, CALL r/m
//
// CS = MEM[31:16] -- IDT LOAD (64), far ret (32)
// CS = MEM[47:32] -- far ret (64), IRETD

   wire [1:0] d2_mem_size_wb_bar;
   wire d2_mem_rd_me_bar;
   wire and0_out, and1_out, and2_out, or0_out,
        and3_out, and4_out, and5_out, and6_out,
        and7_out, or1_out;

   wire [1:0] cs_mux_mem_rd_addr_ag_bar;

   inv1$ inv0 [1:0] (d2_mem_size_wb_bar, D2_MEM_SIZE_WB);
   inv1$ inv1 (d2_mem_rd_me_bar, D2_MEM_RD_ME);
   inv1$ inv2 [1:0] (cs_mux_mem_rd_addr_ag_bar, CS_MUX_MEM_RD_ADDR_AG);

   // CS_IS_NEAR_RET_M2 set for near return only
   // CS_IS_FAR_RET set for far ret and IRETD
   and3$ and0 (and0_out, CS_IS_NEAR_RET_M2, D2_MEM_SIZE_WB[1], d2_mem_size_wb_bar[0]);
   and3$ and1 (and1_out, CS_IS_FAR_RET_M2, D2_MEM_SIZE_WB[1], D2_MEM_SIZE_WB[0]);
   and2$ and2 (and2_out, CS_JMP_STALL_DE, D2_MEM_RD_ME); // CS_JMP_STALL set for JMP and CALL
   or3$ or0 (or0_out, and0_out, and1_out, and2_out);

   // IDT LOAD = ADDR taken from IDT entry
   and2$ and3 (and3_out, CS_MUX_MEM_RD_ADDR_AG[1], cs_mux_mem_rd_addr_ag_bar[0]);

   // JMP MOD_EQ_REG, CALL MOD_EQ_REG
   and2$ and4 (and4_out, CS_JMP_STALL_DE, d2_mem_rd_me_bar);

   // near ret(16), far ret(32)
   //and3$ and5 (and5_out, CS_IS_NEAR_RET_M2, d2_mem_size_wb_bar[1], D2_MEM_SIZE_WB[0]);
   and3$ and6 (and6_out, CS_IS_FAR_RET_M2, D2_MEM_SIZE_WB[1], d2_mem_size_wb_bar[0]);
   and2$ and7 (and7_out, d2_mem_size_wb_bar[1], D2_MEM_SIZE_WB[0]);
   or2$ or1 (or1_out, and6_out, and7_out);

   wire [2:0] neip_sel;
   wire [15:0] mux_neip_high_out, mux_neip_low_out;

   pencoder8_3v$ pencoder_neip (1'b0, {4'b0, or1_out, and4_out, and3_out, or0_out}, neip_sel, );
   mux4_16$ mux_neip_high (mux_neip_high_out, buf_mem_out[31:16], buf_mem_out[63:48], A[31:16], 16'b0, neip_sel[0], neip_sel[1]);

   mux2_16$ mux_neip_low (mux_neip_low_out, buf_mem_out[15:0], A[15:0], and4_out);

   wire [31:0] mux_neip_out;
   // CS_MUX_NEXT_EIP_M2
   mux2_32 mux_neip (mux_neip_out, NEIP, {mux_neip_high_out, mux_neip_low_out}, CS_MUX_NEXT_EIP_M2);

   // CS_MUX_NEXT_CSEG_M2 set for FAR RET and IRETD and IDT load
   wire [15:0] mux_cseg_out, mux_next_cseg_out;
   mux2_16$ mux_cseg (mux_cseg_out, buf_mem_out[31:16], buf_mem_out[47:32], and1_out);
   mux2_16$ mux_next_cseg (mux_next_cseg_out, NCS, mux_cseg_out, CS_MUX_NEXT_CSEG_M2);

   assign NEIP_OUT = mux_neip_out;
   assign NCS_OUT = mux_next_cseg_out;
   assign CONTROL_STORE_OUT = CONTROL_STORE;

   wire [31:0] mem_sext8, mem_sext16;

   assign mem_sext8 = {{24{buf_mem_out[7]}}, {buf_mem_out[7:0]}};
   assign mem_sext16 = {{16{buf_mem_out[15]}}, {buf_mem_out[15:0]}};

   wire [31:0] mux_mem_out;

   mux4_32 mux_mem (mux_mem_out, mem_sext8, mem_sext16, buf_mem_out[31:0], , D2_MEM_SIZE_WB[0], D2_MEM_SIZE_WB[1]);

   wire [31:0] buf_a_out, buf_b_out;
   wire [31:0] a_sext8, a_sext16,
	       b_sext8, b_sext16;

   bufferH64$ buf_a [31:0] (buf_a_out, A);
   bufferH64$ buf_b [31:0] (buf_b_out, B);
   
   assign a_sext8 = {{24{buf_a_out[7]}}, buf_a_out[7:0]};
   assign a_sext16 = {{16{buf_a_out[15]}}, buf_a_out[15:0]};

   assign b_sext8 = {{24{buf_b_out[7]}}, buf_b_out[7:0]};
   assign b_sext16 = {{16{buf_b_out[15]}}, buf_b_out[15:0]};

   wire [31:0] mux_a_sext_out, mux_b_sext_out, mux_a_cmpxchg_out, mux_b_cmpxchg_out;

   mux4_32 mux_a_sext (mux_a_sext_out, a_sext8, a_sext16, buf_a_out, , D2_MEM_SIZE_WB[0], D2_MEM_SIZE_WB[1]);
   mux4_32 mux_b_sext (mux_b_sext_out, b_sext8, b_sext16, buf_b_out, , D2_MEM_SIZE_WB[0], D2_MEM_SIZE_WB[1]);

   mux2_32 mux_a_cmpxchg (mux_a_cmpxchg_out, buf_a_out, mux_a_sext_out, CS_IS_CMPXCHG_EX); 
   mux2_32 mux_b_cmpxchg (mux_b_cmpxchg_out, buf_b_out, mux_b_sext_out, CS_IS_CMPXCHG_EX); 

   mux2_32
      mux_a (A_OUT, mux_a_cmpxchg_out, mux_mem_out, D2_MEM_RD_ME),
      mux_b (B_OUT, mux_b_cmpxchg_out, A, CS_MUX_B_ME);

   wire nor_mm_a_out, and_mm_a_out;
   // if it's a call (any) or IDT LOAD, don't overwrite MM_A (already contains EIP/CS data
   nor2$ nor_mm_a (nor_mm_a_out, CS_JMP_STALL_DE, and3_out);
   and2$ and_mm_a (and_mm_a_out, D2_MEM_RD_ME, nor_mm_a_out);

   mux2_64 mux_mm_a (MM_A_OUT, MM_A, DCACHE_DATA, and_mm_a_out);

   assign MM_B_OUT = MM_B;

   // only for RET imm16 (always unsigned)
   mux2_16$ mux_imm (mux_imm_out, 16'b0, B[15:0], CS_MUX_IMM_ADD_ME);
   adder32_w_carry_in
      add_xchg (SP_XCHG_DATA_OUT, , {16'b0, mux_imm_out}, SP_XCHG_DATA, 1'b0);

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

   wire or_jmp_stall_out;
   or3$ or_jmp_stall (or_jmp_stall_out, CS_JMP_STALL_DE, CS_IS_NEAR_RET_M2, CS_IS_FAR_RET_M2);
   and2$ and_jmp_stall (JMP_STALL_OUT, V, or_jmp_stall_out);

   and3$ and_ld_df (V_LD_DF_OUT, V, CS_LD_FLAGS_WB, CS_FLAGS_AFFECTED_WB[5]);
   
endmodule
