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
    input [1:0] modrm_sel,
    input offset_present,
    input opcode_size, 
    input [1:0] offset_size,
    input [2:0] segID,
    input [7:0] modrm, sib,

    output [31:0] EIP_OUT, 
    output [15:0] CS_OUT,
    output [31:0] control_store,
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

//   assign MOD_EQ_REG = 1'b1;
//   assign MOD_EQ_MEM = 1'b0;
//   assign OPERAND_OVERRIDE_EN = 1'b1;
//   assign DE_SIB_EN = 1'b1;
//
//   assign IR_REG_OP = 3'b000; // REG/OPCODE field
//   assign IR_MOD_RM = 3'b011; // R/M field of MODR/M byte
//   assign IR_SIB_BASE = 3'b010; // SIB Base field 
//   assign opcode = 16'hFC00;
//
//   // directly generated outputs
//   assign DE_BASE_REG_EN_AG = 1'b1;
//   assign DE_MUX_SEG_AG = 1'b1; // select to use SEG1 or CS since already read
//   assign DE_SIB_S_AG = 2'b01; // comes from sib scale field


// Remaining decode fields
// IR_REG_OP

    ucontrol_store u_ucontrol_store (.opcode(opcode), .opcode_size(opcode_size), .control_signal(control_signal));

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
     mux_ld_gpr (D2_LD_GPR1_WB, CS_LD_GPR_DE, MOD_EQ_REG, CS_MUX_LD_GPR_DE);

   mux2$
     mux_base_reg_id [2:0] (mux_base_reg_id_out, IR_MOD_RM, IR_SIB_BASE, DE_SIB_EN),
     mux_sr1_id [2:0] (SR1_OUT, mux_base_reg_id_out, CS_SR1_AG, CS_MUX_SR1_AG),
     mux_sr2_id [2:0] (SR2_OUT, IR_REG_OP, CS_SR2_AG, CS_MUX_SR2_AG),
     mux_seg1_id [2:0] (SEG1_OUT, DE_SEG1_ID, 3'b000, CS_MUX_SEG1_AG), // ES segment register
     mux_seg2_id [2:0] (SEG2_OUT, 3'b010, IR_REG_OP, CS_MUX_SEG2_AG);  // SS segment register

   // LD_MM = CS_LD_MM || (MOD == 2'b11 REG && opcode == 0F7F):MOVQ mm/m64,mm  
   comp16 comp_0F7F (op_0F7F, op_0F7F_bar, opcode, 16'h0F7F);
   and2$ and_ld_mm (and_ld_mm_out, MOD_EQ_REG, op_0F7F);
   or2$ or_ld_mm (D2_LD_MM_WB, CS_LD_MM_DE, and_ld_mm_out);
 
   // SR1_NEEDED = SR1_NEEDED || (CS_MM1_NEEDED && MOD_EQ_MEM): MM INSTs
   and2$ and_sr1_needed (and_sr1_needed_out, CS_MM1_NEEDED_DE, MOD_EQ_MEM);
   or2$ or_sr1_needed (D2_SR1_NEEDED_AG, CS_SR1_NEEDED_DE, and_sr1_needed_out);

   // MM1_NEEDED = (CS_MM1_NEEDED && MOD == 11 REG && OPCODE != 0x0F7F)
   and3$ (D2_MM1_NEEDED_DE, CS_MM1_NEEDED_DE, MOD_EQ_REG, op_0F7F_bar);

   comp16 comp_0FB0 (DE_CMPXCHG_AG, , {opcode[15:1], 1'b0}, 16'h0FB0); // set for cmpxchg


//   register_file u_register_file (clk, set, reset, SR1, SR2, SR3, SR4, DR1, DR2, DR3,
//       write_DR1, write_DR2, write_DR3, result1, result2, result3, write_size, read_size,
//       regA, regB, regC, regD);

endmodule
