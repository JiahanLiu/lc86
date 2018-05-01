module agen_stage1 (
   input CLK, RST, SET, V,

   // Signals to be saved in pipeline latches
   input [31:0] EIP, 
   input [15:0] CS,
   input [127:0] CONTROL_STORE,

   input [47:0] OFFSET,
   input D2_REPNE_WB,
			   
   input D2_SR1_NEEDED_AG, D2_SEG1_NEEDED_AG, D2_MM1_NEEDED_AG,

   input D2_MEM_RD_ME, D2_MEM_WR_ME,
   input [2:0] D2_ALUK_EX,
   input D2_LD_GPR1_WB, D2_LD_MM_WB,

   input [2:0] SR1, SR2, SR3, SIB_I, SEG1, SEG2,

   input [1:0] D2_SR1_SIZE_AG, D2_SR2_SIZE_AG,
   input [1:0] D2_DR1_SIZE_WB, D2_DR2_SIZE_WB,
   input [1:0] D2_MEM_SIZE_WB,

   input [31:0] IMM32, DISP32,

   input DE_SIB_EN_AG, DE_DISP_EN_AG, DE_BASE_REG_EN_AG,
   input DE_MUX_SEG_AG, DE_CMPXCHG_AG,
   input [1:0] DE_SIB_S_AG,

   input [31:0] SR1_DATA, SR2_DATA, SR3_DATA, SIB_I_DATA,
   input [15:0] SEG1_DATA, SEG2_DATA,
   input [63:0] MM1_DATA, MM2_DATA,

   // EXCEPTION/INTERRUPT STATUS
   input NMI_INT_EN, GEN_PROT_EXC_EN, PAGE_FAULT_EXC_EN,
   input PAGE_FAULT_EXC_EXIST,
		    
   // Dependency check inputs
   input AG2_V,
   input [23:0] AG2_GPR_SCOREBOARD,
   input [7:0] AG2_SEG_SCOREBOARD,
   input [7:0] AG2_MM_SCOREBOARD,
		    
   input ME_V,
   input [23:0] ME_GPR_SCOREBOARD,
   input [7:0] ME_SEG_SCOREBOARD,
   input [7:0] ME_MM_SCOREBOARD,

   input ME2_V,
   input [23:0] ME2_GPR_SCOREBOARD,
   input [7:0] ME2_SEG_SCOREBOARD,
   input [7:0] ME2_MM_SCOREBOARD,
		    
   input EX_V,
   input [23:0] EX_GPR_SCOREBOARD,
   input [7:0] EX_SEG_SCOREBOARD,
   input [7:0] EX_MM_SCOREBOARD,

   // Signals to register file
   output [2:0] SR1_OUT, SR2_OUT, SR3_OUT, SIB_I_OUT, SEG1_OUT, SEG2_OUT, MM1_OUT, MM2_OUT,

   output [1:0] D2_SR1_SIZE_AG_OUT, D2_SR2_SIZE_AG_OUT,
   output [1:0] D2_SR3_SIZE_AG_OUT, D2_SR4_SIZE_AG_OUT,
   output [1:0] D2_DR1_SIZE_WB_OUT, D2_DR2_SIZE_WB_OUT,
   output [1:0] D2_MEM_SIZE_WB_OUT,

   // Signals for next stage latches
   output [31:0] EIP_OUT,
		    
   output [31:0] NEIP_OUT, 
   output [15:0] NCS_OUT,
   output [127:0] CONTROL_STORE_OUT,

   output [31:0] A_OUT, B_OUT,
   output [63:0] MM_A_OUT, MM_B_OUT,
   output [31:0] SP_XCHG_DATA_OUT,
   output [31:0] ADD_BASE_DISP_OUT, ADD_SIB_SEG1_OUT,
   output [31:0] SIB_SI_DATA_OUT,
   output [15:0] SEG2_DATA_OUT,
   output [31:0] INTERRUPT_ADDR_OUT,
		    
   output [2:0] D2_ALUK_EX_OUT,
   output [2:0] DRID1_OUT, DRID2_OUT,

   output D2_MEM_RD_ME_OUT, D2_MEM_WR_WB_OUT,
   output D2_LD_GPR1_WB_OUT, D2_LD_MM_WB_OUT,

   output [23:0] GPR_SCOREBOARD_OUT,
   output [7:0] SEG_SCOREBOARD_OUT,
   output [7:0] MM_SCOREBOARD_OUT,

   // Other signals
   output DEP_STALL_OUT, PAGE_FAULT_EXC_EXIST_OUT, AG1_REPNE_WB
);
//`include "ag_control_store.v"
`include "./control_store/control_store_wires.v"
`include "./control_store/control_store_signals.v"

   wire [31:0] mux_rel_out, add_rel_out;
   wire [31:0] mux_disp_out, mux_base_reg_out, add_base_disp_out;
   wire [31:0] shf_sib_idx_out, mux_sib_si_out, add_sib_seg1_out;
   wire [15:0] mux_seg1_out;

   wire [3:0] mux_push_size_out;
   wire [31:0] mux_push_add_out, add_sp_out;

//   wire [31:0] shf_exc_code_out, add_idt_base_out;

    assign AG1_REPNE_WB = D2_REPNE_WB;
   assign SR1_OUT = SR1;
   assign SR2_OUT = SR2;
   assign SR3_OUT = SR3;
   assign SIB_I_OUT = SIB_I;
   assign SEG1_OUT = SEG1;
   assign SEG2_OUT = SEG2;
   assign MM1_OUT = SR1;
   assign MM2_OUT = SR2;

   assign D2_SR1_SIZE_AG_OUT = D2_SR1_SIZE_AG;
   assign D2_SR2_SIZE_AG_OUT = D2_SR2_SIZE_AG;

   wire [1:0] sr3_size, sib_i_size;
   assign sr3_size = D2_SR2_SIZE_AG;
   assign sib_i_size = 2'b10; // always 32-bits

   assign D2_SR3_SIZE_AG_OUT = D2_SR2_SIZE_AG; // only used in CMPXCHG, same size as EAX in SR2
   assign D2_SR4_SIZE_AG_OUT = sib_i_size;

   assign D2_DR1_SIZE_WB_OUT = D2_DR1_SIZE_WB;
   assign D2_DR2_SIZE_WB_OUT = D2_DR2_SIZE_WB;
   assign D2_MEM_SIZE_WB_OUT = D2_MEM_SIZE_WB;

   assign EIP_OUT = EIP; // for segment limit check
   
   // Generate next EIP value
   mux2_32 mux_rel (mux_rel_out, 32'b0, OFFSET[31:0], CS_MUX_EIP_JMP_REL_AG);
   adder32_w_carry_in add_rel (add_rel_out, , EIP, mux_rel_out, 1'b0);
   mux2_32 mux_eip (NEIP_OUT, add_rel_out, OFFSET[31:0], CS_MUX_NEXT_EIP_AG);

   // Generate next CS register value
   mux2_16$ mux_cseg (NCS_OUT, CS, OFFSET[47:32], CS_MUX_NEXT_CSEG_AG);
   
   assign CONTROL_STORE_OUT = CONTROL_STORE;

   // Generate A and B latch values
   mux4_32
      mux_a (A_OUT, SR1_DATA, {16'b0, SEG1_DATA}, {16'b0, SEG2_DATA}, {16'b0, CS}, CS_MUX_A_AG[0], CS_MUX_A_AG[1]);

   mux2_32
      mux_b (B_OUT, SR2_DATA, IMM32, CS_MUX_B_AG);

   assign MM_A_OUT = MM1_DATA;
   assign MM_B_OUT = MM2_DATA;

   // Generate SR1 address
   mux2_32
      mux_disp (mux_disp_out, 32'b0, DISP32, DE_DISP_EN_AG),
      mux_base_reg (mux_base_reg_out, 32'b0, SR1_DATA, DE_BASE_REG_EN_AG);
   adder32_w_carry_in add_base_disp (add_base_disp_out, , mux_disp_out, mux_base_reg_out, 1'b0); 
   assign ADD_BASE_DISP_OUT = add_base_disp_out;
   
   sal32 shf_sib_idx (shf_sib_idx_out, SIB_I_DATA, {3'b0, DE_SIB_S_AG});
   mux2_32 mux_sib_si (mux_sib_si_out, 32'b0, shf_sib_idx_out, DE_SIB_EN_AG);
   mux2_16$ mux_seg1 (mux_seg1_out, SEG1_DATA, CS, DE_MUX_SEG_AG);

   adder32_w_carry_in add_sib_seg1 (add_sib_seg1_out, , {mux_seg1_out, 16'b0}, mux_sib_si_out, 1'b0);
//   adder32_w_carry_in add_seg1 (add_seg1_out, , add_base_disp_out, add_sib_seg1_out, 1'b0);
   assign ADD_SIB_SEG1_OUT = add_sib_seg1_out;
   assign SIB_SI_DATA_OUT = mux_sib_si_out;

   assign SEG2_DATA_OUT = SEG2_DATA;
   
   // Generate SR2 address (for stack accesses)
//   mux2$
//     mux_push_size [1:0] (mux_push_size_out, 2'b10, 2'b00, DATA_SIZE[1]); // select to add -2 or -4 on data size
// -2 = 1110; -4 = 1100; -8 = 1000
   mux4_4 mux_push_size (mux_push_size_out, , 4'b1110, 4'b1100, 4'b1000, D2_MEM_SIZE_WB[0], D2_MEM_SIZE_WB[1]);
   mux2_32 mux_push_add (mux_push_add_out, 32'b0, {28'b1, mux_push_size_out}, CS_MUX_SP_PUSH_AG);
   adder32_w_carry_in add_sp (add_sp_out, , SR2_DATA, mux_push_add_out, 1'b0);
//   adder32_w_carry_in add_seg2 (add_seg2_out, , {SEG2_DATA, 16'b0}, add_sp_out, 1'b0);
   mux2_32 mux_sp_xchg (SP_XCHG_DATA_OUT, add_sp_out, SR3_DATA, CS_IS_CMPXCHG_EX);
   
   // Generate IDTR + offset address (for IDT entry reads)
//   sal32 shf_exc_code (shf_exc_code_out, {28'b0, DE_EXC_CODE_AG}, 5'b00011);
//   adder32_w_carry_in add_idt_base (add_idt_base_out, , `IDTR_VAL, shf_exc_code_out, 1'b0);
   wire [7:0] interrupt_status = {5'b0, GEN_PROT_EXC_EN, PAGE_FAULT_EXC_EN, NMI_INT_EN};
   wire [2:0] int_encode;
   wire [31:0] mux_int_addr_out;
   pencoder8_3v$ pencoder_int (1'b0, interrupt_status, int_encode, );
   mux4_32 mux_int_addr (mux_int_addr_out, `IDT_NMI_INT_VECTOR, `IDT_PAGE_FAULT_VECTOR, `IDT_GEN_PROT_VECTOR, , int_encode[0], int_encode[1]);
   assign INTERRUPT_ADDR_OUT = mux_int_addr_out;
   
   // Decide MEM_RD_ADDR, MEM_WR_ADDR - Moved to AG2
//   mux4_32
//      mux_rd_addr [31:0] (MEM_RD_ADDR_OUT, add_seg1_out, add_seg2_out, mux_int_addr_out, , CS_MUX_MEM_RD_ADDR_AG[0], CS_MUX_MEM_RD_ADDR_AG[1]),
//      mux_wr_addr [31:0] (MEM_WR_ADDR_OUT, add_seg1_out, add_seg2_out, , , CS_MUX_MEM_WR_ADDR_AG[0], CS_MUX_MEM_WR_ADDR_AG[1]);

   assign D2_ALUK_EX_OUT = D2_ALUK_EX;
   mux2_3 mux_drid1 (DRID1_OUT, SR1, SR2, CS_MUX_DRID1_AG);
   assign DRID2_OUT = SR2;

   assign D2_MEM_RD_ME_OUT = D2_MEM_RD_ME;
   assign D2_MEM_WR_WB_OUT = D2_MEM_WR_ME;
   
   assign D2_LD_GPR1_WB_OUT = D2_LD_GPR1_WB; 
   assign D2_LD_MM_WB_OUT = D2_LD_MM_WB;
   
   reg_dependency_check u_reg_dependency_check (
      V, SR1, SR2, SR3, SIB_I, SEG1, SEG2,
      D2_SR1_SIZE_AG, D2_SR2_SIZE_AG, sr3_size, sib_i_size,
      D2_SR1_NEEDED_AG, CS_SR2_NEEDED_AG, CS_IS_CMPXCHG_EX, DE_SIB_EN_AG,
      D2_SEG1_NEEDED_AG, CS_SEG2_NEEDED_AG, D2_MM1_NEEDED_AG, CS_MM2_NEEDED_AG,
      AG2_V, AG2_GPR_SCOREBOARD, AG2_SEG_SCOREBOARD, AG2_MM_SCOREBOARD,
      ME_V, ME_GPR_SCOREBOARD, ME_SEG_SCOREBOARD, ME_MM_SCOREBOARD,
      ME2_V, ME_GPR_SCOREBOARD, ME2_SEG_SCOREBOARD, ME2_MM_SCOREBOARD,
      EX_V, EX_GPR_SCOREBOARD, EX_SEG_SCOREBOARD, EX_MM_SCOREBOARD,
      DEP_STALL_OUT
   );

// MOVED TO AG2 
//   segment_limit_check u_seg_limit_check (
//      V, D2_MEM_RD_ME, D2_MEM_WR_ME, CS_MUX_MEM_RD_ADDR_AG, CS_MUX_MEM_WR_ADDR_AG,
//      SEG1, DATA_SIZE, add_base_disp_out, mux_sib_si_out,
//      SEG_LIMIT_EXC_OUT
//   );

   all_scoreboard_generator u_all_scoreboard_generator (
      V,
      DRID1_OUT, DRID2_OUT, CS_DR3_D2,
      D2_DR1_SIZE_WB, D2_DR2_SIZE_WB, 2'b10,
      D2_LD_GPR1_WB, CS_LD_GPR2_EX, CS_LD_GPR3_WB,
      CS_LD_SEG_WB, CS_LD_CS_WB,
      D2_LD_MM_WB,
      GPR_SCOREBOARD_OUT,
      SEG_SCOREBOARD_OUT,
      MM_SCOREBOARD_OUT
   );

   // pass through whatever was given
   assign PAGE_FAULT_EXC_EXIST_OUT = PAGE_FAULT_EXC_EXIST;
   
endmodule
