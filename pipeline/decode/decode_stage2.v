module decode_stage2 (
    input clk, set, reset,
    input [127:0] IR, 
    input [31:0] EIP,
    input [15:0] CS,
    input [3:0] instr_length_updt,
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
    output [127:0] CONTROL_STORE,
    output [47:0] offset,

    output [1:0] D2_DATA_SIZE_AG,
   output D2_SR1_NEEDED_AG, D2_SEG1_NEEDED_AG, D2_MM1_NEEDED_AG,

   output D2_MEM_RD_ME, D2_MEM_WR_ME, 
   output [2:0] D2_ALUK_EX,
   output D2_LD_GPR1_WB, D2_LD_MM_WB,

    output [2:0] SR1_OUT, SR2_OUT, SR3_OUT, SR4_OUT, SEG1_OUT, SEG2_OUT,
   output [31:0] IMM32_OUT, DISP32_OUT,

   output DE_SIB_EN_AG, DE_DISP_EN_AG, DE_BASE_REG_EN_AG,
   output DE_MUX_SEG_AG, DE_CMPXCHG_AG,
   output [1:0] DE_SIB_S_AG

);
`include "./control_store/control_store_wires.v"
`include "./control_store/control_store_signals.v"
   wire [2:0] mux_base_reg_id_out;
   wire op_0F7F, op_0F7F_bar, and_ld_mm_out, and_sr1_needed_out;

   wire MOD_EQ_REG, MOD_EQ_MEM;
   wire OPERAND_OVERRIDE_EN;
   wire [2:0] IR_REG_OP, IR_MOD_RM, IR_SIB_BASE; 


   // 32-bit disp, imm and 48-bit offset selection
   // Need to send the offset bits to disp and imm field based on opcode
   disp_selector u_disp_selector (.IR(IR), .disp_sel(disp_sel), .disp_size(disp_size), .disp(DISP32_OUT) );
   imm_selector u_imm_selector (.IR(IR), .opcode(opcode), .imm_sel(imm_sel), .imm_size(imm_size), .imm(IMM32_OUT) );
   offset_selector u_offset_selector (.IR(IR), .off_sel(modrm_sel), .offset_size(offset_size), .offset(offset) );

   assign OPERAND_OVERRIDE_EN = operand_override;
   assign DE_SIB_EN_AG = sib_present;
   assign DE_DISP_EN_AG = disp_present;


// Remaining decode fields
    assign IR_REG_OP = modrm[5:3];
    assign IR_MOD_RM = modrm[2:0];
    assign IR_SIB_BASE = sib[2:0];
    assign DE_SEG1_ID = 3'b000;

    ucontrol_store u_ucontrol_store2 (.opcode(opcode[7:0]), .opcode_size(opcode_size), .control_signal(CONTROL_STORE[63:0]));
    ucontrol_store u_ucontrol_store1 (.opcode(opcode[7:0]), .opcode_size(opcode_size), .control_signal(CONTROL_STORE[127:64]));

    inv1$ inv1 (mod7_b, modrm[7]);
    inv1$ inv2 (mod6_b, modrm[6]);

    or2$ or1 (MOD_EQ_MEM, mod7_b, mod6_b);
    and2$ and1 (MOD_EQ_REG, modrm[7], modrm[6]);

    // SegID override EBP, ESP
    // mod=01,10 and rm = 101 and modrm_present- segID=SS
    // sib_present and base=100, segID=SS
    inv1$ inv1s (sib0_b, sib[0]);
    inv1$ inv2s (sib1_b, sib[1]);
    inv1$ inv3s (modrm1_b, modrm[1]);

    and4$ and1p (sib_seg_ovr, sib_present, sib0_b, sib1_b, sib[2]);
    xor2$ xor2p (out2p, modrm[7], modrm[6]);
    and3$ and3p (out3p, modrm[0], modrm1_b, modrm[2]);
    and3$ and4p (mod_seg_ovr, modrm_present, out2p, out3p); 

    // DE_BASE_REG_EN_AG=1 when mod=00 and rm=101 - disp32, base not required
    inv1$ inv3k (modrm7_b, modrm[7]);
    inv1$ inv4k (modrm6_b, modrm[6]);
    and3$ and3k (DE_BASE_REG_EN_AG, out3p, modrm7_b, modrm6_b);

    inv1$ inv1k (segID2_b, segID[2]);
    inv1$ inv2k (segID1_b, segID[1]);

    and3$ and1k (DE_MUX_SEG_AG, segID2_b, segID1_b, segID[0]); // CS override
    assign DE_SIB_S_AG = sib[7:6];
    assign SR3_OUT = modrm[5:3];
    assign SR4_OUT = sib[5:3];

    // SegID override for PUSH, POP - instr_seg_ovr
    
//    mux2$ muxs1[2:0] (DE_SEG1_ID, segID, 3'b010, seg_ovr_overall);

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
     mux_base_reg_id [2:0] (mux_base_reg_id_out, IR_MOD_RM, IR_SIB_BASE, DE_SIB_EN_AG),
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
   and3$ and2 (D2_MM1_NEEDED_AG, CS_MM1_NEEDED_AG, MOD_EQ_REG, op_0F7F_bar);

   comp16 comp_0FB0 (DE_CMPXCHG_AG, , {opcode[15:1], 1'b0}, 16'h0FB0); // set for cmpxchg

   // Increment the EIP with proper length
   adder32_w_carry_in add_rel (EIP_OUT, , EIP, {28'b0, instr_length_updt}, 1'b0);

endmodule
