module decode_stage2 (
    input clk, set, reset,
    input [127:0] IR, 
    input [31:0] EIP,
    input [15:0] CS,
    input [15:0] opcode, 
    input [1:0] prefix_size,
    input prefix_present, segment_override, operand_override, repeat_prefix, 
    input modrm_present, imm_present,
    input [1:0] imm_size,
    input sib_present, disp_present, disp_size,
    input [3:0] imm_sel,
    input [2:0] disp_sel,
    input [2:0] modrm_sel,
    input offset_present,
    input opcode_size, 
    input [1:0] offset_size,
    input [2:0] segID,
    input [7:0] modrm, sib,

    output [31:0] EIP_OUT, 
    output [15:0] CS_OUT,
    output [63:0] control_signal,
    output [2:0] DR, SR, base, index,
    output [2:0] MM_DR, MM_SR,
    output [2:0] seg_SR, seg_DR,
    output [1:0] data_size, 
    output [31:0] imm, disp,

    output operation, MM_operation,
    output type_A, MM_type_A,
    output type_B, MM_type_B,
    output [1:0] D2_DATA_SIZE_AG,
   output D2_SR1_NEEDED_AG, D2_SEG1_NEEDED_AG, D2_MM1_NEEDED_AG,

   output D2_MEM_RD_ME, D2_MEM_WR_ME, 
   output [2:0] D2_ALUK_EX,
   output D2_LD_GPR1_WB, D2_LD_MM_WB,

   output [2:0] SR1_OUT, SR2_OUT, SEG1_OUT, SEG2_OUT,
   output [31:0] IMM32_OUT, DISP32_OUT,

   output DE_SIB_EN_AG, DE_DISP_EN_AG, DE_BASE_REG_EN_AG,
   output DE_MUX_SEG_AG, DE_CMPXCHG_AG,
   output [1:0] DE_SIB_S_AG

);

   wire [2:0] mux_base_reg_id_out;
   wire op_0F7F, op_0F7F_bar, and_ld_mm_out, and_sr1_needed_out;

   wire MOD_EQ_REG, MOD_EQ_MEM;
   wire OPERAND_OVERRIDE_EN, DE_SIB_EN;
   wire [2:0] IR_REG_OP, IR_MOD_RM, IR_SIB_BASE; 

   wire [47:0] offset;

   // 32-bit disp, imm and 48-bit offset selection
   // Need to send the offset bits to disp and imm field based on opcode
   disp_selector u_disp_selector (.IR(IR), .disp_sel(disp_sel), .disp_size(disp_size), .disp(disp) );
   imm_selector u_imm_selector (.IR(IR), .opcode(opcode), .imm_sel(imm_sel), .imm_size(imm_size), .imm(imm) );
   offset_selector u_offset_selector (.IR(IR), .off_sel(modrm_sel), .offset_size(offset_size), .offset(offset) );

   assign OPERAND_OVERRIDE_EN = operand_override;
   assign DE_SIB_EN = sib_present;
   assign DE_DISP_EN_AG = disp_present;

//   assign IR_REG_OP = 3'b000; // REG/OPCODE field
//   assign IR_MOD_RM = 3'b011; // R/M field of MODR/M byte
//   assign IR_SIB_BASE = 3'b010; // SIB Base field 
//
//   // directly generated outputs
//   assign DE_BASE_REG_EN_AG = 1'b1;
//   assign DE_MUX_SEG_AG = 1'b1; // select to use SEG1 or CS since already read
//   assign DE_SIB_S_AG = 2'b01; // comes from sib scale field


// Remaining decode fields
    assign IR_REG_OP = modrm[5:3];
    assign IR_MOD_RM = modrm[7:6];
    assign IR_SIB_BASE = sib[2:0];
    assign DE_SEG1_ID = 3'b000;

    ucontrol_store u_ucontrol_store (.opcode(opcode[7:0]), .opcode_size(opcode_size), .control_signal(control_signal));

    // Control signals
    assign CS_UOP_STALL_DE = control_signal[0];
    assign CS_DATA_SIZE_DE = control_signal[1];
    assign CS_MUX_ALUK_DE = control_signal[2];
    assign CS_ALUK_DE = control_signal[3];
    assign CS_MUX_LD_GPR1_DE = control_signal[4];
    assign CS_LD_GPR1_DE = control_signal[5];
    assign CS_MUX_MEM_RD_DE = control_signal[6];
    assign CS_MEM_RD_DE = control_signal[7];
    assign CS_MUX_MEM_WR_DE = control_signal[8];
    assign CS_MEM_WR_DE = control_signal[9];
    assign CS_JMP_STALL_DE = control_signal[10];
    assign CS_MUX_SR1_D2 = control_signal[11];
    assign CS_SR1_D2 = control_signal[12];
    assign CS_MUX_SR2_D2 = control_signal[13];
    assign CS_SR2_D2 = control_signal[14];
    assign CS_MUX_SEG1_D2 = control_signal[15];
    assign CS_MUX_SEG2_D2 = control_signal[16];
    assign CS_SR1_NEEDED_AG = control_signal[17];
    assign CS_SR2_NEEDED_AG = control_signal[18];
    assign CS_MUX_SEG1_NEEDED_AG = control_signal[19];
    assign CS_SEG1_NEEDED_AG = control_signal[20];
    assign CS_SEG2_NEEDED_AG = control_signal[21];
    assign CS_MM1_NEEDED_AG = control_signal[22];
    assign CS_MM2_NEEDED_AG = control_signal[23];
    assign CS_MUX_A_AG = control_signal[24];
    assign CS_MUX_B_AG = control_signal[25];
    assign CS_MUX_DRID1_AG = control_signal[26];
    assign CS_MUX_EIP_JMP_REL_AG = control_signal[27];
    assign CS_MUX_NEXT_EIP_AG = control_signal[28];
    assign CS_MUX_NEXT_CSEG_AG = control_signal[29];
    assign CS_MUX_SP_PUSH_AG = control_signal[30];
    assign CS_MUX_MEM_RD_ADDR_AG = control_signal[31];
    assign CS_MUX_MEM_WR_ADDR_AG = control_signal[32];
    assign CS_MUX_SP_XCHG_DATA_AG = control_signal[33];
    assign CS_MUX_B_ME = control_signal[34];
    assign CS_MUX_IMM_ADD_ME = control_signal[35];
    assign CS_MUX_SP_POP_EX = control_signal[36];
    assign CS_LD_TEMP_EX = control_signal[37];
    assign CS_MUX_B_EX = control_signal[38];
    assign CS_MUX_RESULT_EX = control_signal[39];
    assign CS_MUX_SR1_DATA_EX = control_signal[40];
    assign CS_MUX_SP_XCHG_DATA_EX = control_signal[41];
    assign CS_MUX_NEXT_EIP_EX = control_signal[42];
    assign CS_MUX_NEXT_CSEG_EX = control_signal[43];
    assign CS_MUX_SR1_MEM_DATA_WB = control_signal[44];
    assign CS_LD_GPR2_WB = control_signal[45];
    assign CS_LD_SEG_WB = control_signal[46];
    assign CS_LD_CSEG_WB = control_signal[47];
    assign CS_LD_MM_WB = control_signal[48];
    assign CS_LD_EIP_WB = control_signal[49];
    assign CS_LD_FLAGS_WB = control_signal[50];
    assign PLACEHOLDER = control_signal[51];
    assign PLACEHOLDER2 = control_signal[52];

    inv1$ inv1 (mod7_b, modrm[7]);
    inv1$ inv2 (mod6_b, modrm[6]);

    or2$ or1 (MOD_EQ_MEM, mod7_b, mod6_b);
    and2$ and1 (MOD_REQ_MEM, modrm[7], modrm[6]);

//module  mux2$(outb, in0, in1, s0);
   mux2$
     mux_data_size [1:0] (D2_DATA_SIZE_AG, CS_DATA_SIZE_DE, 2'b01, OPERAND_OVERRIDE_EN),
     mux_seg1_needed (D2_SEG1_NEEDED_AG, CS_SEG1_NEEDED_AG, MOD_EQ_MEM, CS_MUX_SEG1_NEEDED_AG),
     mux_mem_rd (D2_MEM_RD_ME, CS_MEM_RD_DE, MOD_EQ_MEM, CS_MUX_MEM_RD_DE),
     mux_mem_wr (D2_MEM_WR_ME, CS_MEM_WR_DE, MOD_EQ_MEM, CS_MUX_MEM_WR_DE),
     mux_aluk [2:0] (D2_ALUK_EX, CS_ALUK_DE, IR_REG_OP, CS_MUX_ALUK_DE),
     mux_ld_gpr (D2_LD_GPR1_WB, CS_LD_GPR1_DE, MOD_EQ_REG, CS_MUX_LD_GPR1_DE);
// CS_MUX_SR1_D2 == CS_MUX_SR1_AG??, CS_SR1_D2 == CS_SR1_AG??
   mux2$
     mux_base_reg_id [2:0] (mux_base_reg_id_out, IR_MOD_RM, IR_SIB_BASE, DE_SIB_EN),
     mux_sr1_id [2:0] (SR1_OUT, mux_base_reg_id_out, CS_SR1_D2, CS_MUX_SR1_D2),
     mux_sr2_id [2:0] (SR2_OUT, IR_REG_OP, CS_SR2_D2, CS_MUX_SR2_D2),
     mux_seg1_id [2:0] (SEG1_OUT, DE_SEG1_ID, 3'b000, CS_MUX_SEG1_D2), // ES segment register
     mux_seg2_id [2:0] (SEG2_OUT, 3'b010, IR_REG_OP, CS_MUX_SEG2_D2);  // SS segment register

   // LD_MM = CS_LD_MM || (MOD == 2'b11 REG && opcode == 0F7F):MOVQ mm/m64,mm  
   comp16 comp_0F7F (op_0F7F, op_0F7F_bar, opcode, 16'h0F7F);
   and2$ and_ld_mm (and_ld_mm_out, MOD_EQ_REG, op_0F7F);
   or2$ or_ld_mm (D2_LD_MM_WB, CS_LD_MM_WB, and_ld_mm_out);
 
   //CS_MM1_NEEDED_DE??, CS_SR1_NEEDED_DE?? CS_LD_MM_DE??
   // SR1_NEEDED = SR1_NEEDED || (CS_MM1_NEEDED && MOD_EQ_MEM): MM INSTs
   and2$ and_sr1_needed (and_sr1_needed_out, CS_MM1_NEEDED_AG, MOD_EQ_MEM);
   or2$ or_sr1_needed (D2_SR1_NEEDED_AG, CS_SR1_NEEDED_AG, and_sr1_needed_out);

   // MM1_NEEDED = (CS_MM1_NEEDED && MOD == 11 REG && OPCODE != 0x0F7F)
   and3$ and2 (D2_MM1_NEEDED_DE, CS_MM1_NEEDED_AG, MOD_EQ_REG, op_0F7F_bar);

   comp16 comp_0FB0 (DE_CMPXCHG_AG, , {opcode[15:1], 1'b0}, 16'h0FB0); // set for cmpxchg


//   register_file u_register_file (clk, set, reset, SR1, SR2, SR3, SR4, DR1, DR2, DR3,
//       write_DR1, write_DR2, write_DR3, result1, result2, result3, write_size, read_size,
//       regA, regB, regC, regD);

endmodule
