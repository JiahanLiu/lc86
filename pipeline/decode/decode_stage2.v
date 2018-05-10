module decode_stage2 (
   input clk, set, reset,
   input D2_V, AG_STALL_OUT_LD_D2_IN,
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
   input [7:0] decode_address,

   input NMI_INT_EN, 
   input GEN_PROT_EXC_EN, 
   input PAGE_FAULT_EXC_EN,
   input PAGE_FAULT_EXC_EXIST,

   input INT_EXIST, WB_REPNE_TERMINATE_ALL,

   output [31:0] EIP_OUT, 
   output [15:0] CS_OUT,
   output [127:0] CONTROL_STORE,
   output [47:0] offset,

   output [1:0] D2_SR1_SIZE_AG_OUT, D2_SR2_SIZE_AG_OUT,
   output [1:0] D2_DR1_SIZE_WB_OUT, D2_DR2_SIZE_WB_OUT,
   output [1:0] D2_MEM_SIZE_WB_OUT,

   output D2_SR1_NEEDED_AG, D2_SEG1_NEEDED_AG, D2_MM1_NEEDED_AG,

   output D2_MEM_RD_ME, D2_MEM_WR_ME, 
   output [2:0] D2_ALUK_EX,
   output D2_LD_GPR1_WB, D2_LD_MM_WB,

   output [2:0] SR1_OUT, SR2_OUT, SR3_OUT, SR4_OUT, SEG1_OUT, SEG2_OUT,
   output [31:0] IMM32_OUT, DISP32_OUT,

   output DE_SIB_EN_AG, DE_DISP_EN_AG, DE_BASE_REG_EN_AG,
   output DE_MUX_SEG_AG, DE_CMPXCHG_AG,
   output [1:0] DE_SIB_S_AG,

   output PAGE_FAULT_EXC_EXIST_OUT,
   output NMI_INT_EN_OUT, GEN_PROT_EXC_EN_OUT, PAGE_FAULT_EXC_EN_OUT,
   output D2_REPNE_WB, D2_UOP_STALL_OUT, D2_EXC_EN_V_OUT,

   output D2_JMP_STALL_OUT,
   output [7:0] D2_control_address_debug
);
`include "../pipeline/control_store/control_store_wires.v"
`include "../pipeline/control_store/control_store_signals.v"
   wire [2:0] mux_base_reg_id_out;
   wire op_0F7F, op_0F7F_bar, and_ld_mm_out, and_sr1_needed_out;

   wire MOD_EQ_REG, MOD_EQ_MEM;
   wire OPERAND_OVERRIDE_EN;
   wire [2:0] IR_REG_OP, IR_MOD_RM, IR_SIB_BASE; 

   wire outs1, outs2, outs4, outs5, outs7, outs8, outs9, outs10, outs11, outs12, outs13;
   wire [2:0] pp_ovr;
   wire push_pop_override;
   wire op7_b, op6_b, op5_b, op4_b, op3_b, op2_b, op1_b, op0_b;
   wire out1o, out2o, offset_ovr, ss_override;
   wire [2:0] segID_mux1;

   assign D2_REPNE_WB = repeat_prefix;

   assign CS_OUT = CS;
   and4$ and1o (out1o, opcode[7], opcode[6], opcode[5], op4_b);
   and4$ and2o (out2o, opcode[3], op2_b, opcode[1], op0_b);
   and3$ and3o (offset_ovr, out1o, out2o, operand_override);

   // 32-bit disp, imm and 48-bit offset selection
   // Need to send the offset bits to disp and imm field based on opcode
   disp_selector u_disp_selector (.IR(IR), .disp_sel(disp_sel), .disp_size(disp_size), .disp(DISP32_OUT) );
   imm_selector u_imm_selector (.IR(IR), .opcode(opcode), .imm_sel(imm_sel), .imm_size(imm_size), .imm(IMM32_OUT) );
   offset_selector u_offset_selector (.IR(IR), .off_sel(modrm_sel), .offset_size(offset_size), .ovr(offset_ovr), .offset(offset) );

   assign OPERAND_OVERRIDE_EN = operand_override;
   assign DE_SIB_EN_AG = sib_present;
   assign DE_DISP_EN_AG = disp_present;


// Remaining decode fields
    assign IR_REG_OP = modrm[5:3];
    assign IR_MOD_RM = modrm[2:0];
    assign IR_SIB_BASE = sib[2:0];
    wire [2:0] DE_SEG1_ID;
    assign DE_SIB_S_AG = sib[7:6];
    assign SR3_OUT = modrm[5:3];
    assign SR4_OUT = sib[5:3];

//   if(opcode == 16'h00FF) begin
//       if(IR_REG_OP == 3'h2)
//           control_address = 5'h1A;
//       else if(IR_REG_OP == 3'h0)
//           control_address = 5'h18;
//       else if(IR_REG_OP == 3'h4)
//           control_address = 5'h1C;
//       else if(IR_REG_OP == 3'h1E)
//           control_address = 5'h1E);
//       else 
//           control_address = opcode[4:0];
//   end

    wire [31:0] Dnext_micro_addr, Qnext_micro_addr;
    wire [7:0] next_micro_op_address;

    wire and_d2_v_ld_out;
    and2$ and_d2_v_ld (and_d2_v_ld_out, D2_V, AG_STALL_OUT_LD_D2_IN);

    assign Dnext_micro_addr = {25'b0, CS_NEXT_MICRO_ADDRESS_DE};
    reg32e$ reg_save_next_uaddr (clk, Dnext_micro_addr, Qnext_micro_addr, , reset, set, and_d2_v_ld_out);
    assign next_micro_op_address = {1'b0, Qnext_micro_addr[6:0]};

    wire [31:0] Dsel_uop, Qsel_uop;
    wire sel_uop;

    wire and_sel_uop_out, nor_int_exist_bar;
    nor2$ nor_int_exist (nor_int_exist_bar, INT_EXIST, WB_REPNE_TERMINATE_ALL);
    and3$ and_sel_uop (and_sel_uop_out, D2_V, CS_UOP_STALL_DE, nor_int_exist_bar);
    assign Dsel_uop = {31'b0, and_sel_uop_out};
    //reg32e$ reg_save_sel_uop (clk, Dsel_uop, Qsel_uop, , reset, set, 1'b1);
    reg32e$ reg_save_sel_uop (clk, Dsel_uop, Qsel_uop, , reset, set, AG_STALL_OUT_LD_D2_IN);
    assign sel_uop = Qsel_uop[0];
     //assign sel_uop = 1'b0; //TODO temporary

    // Mux for choosing the control address, the sel signal needs to be
    // generated -TODO
    // mux4_8$ mux1_cntrl_addr (control_store_address, decode_address, interrupt_address, next_micro_op_address, sel0, sel1);
    // ucontrol_store u_ucontrol_store2 (.opcode(decode_address), .opcode_size(opcode_size), .control_signal(CONTROL_STORE[63:0]));
    // ucontrol_store u_ucontrol_store1 (.opcode(decode_address), .opcode_size(opcode_size), .control_signal(CONTROL_STORE[127:64]));

    wire [7:0] control_store_address;
    assign D2_control_address_debug = control_store_address;
    wire control_store_op_size;

    mux2_8$ muxl_cntrl_addr (control_store_address, decode_address, next_micro_op_address, sel_uop);
    mux2$ mux_opcode_size (control_store_op_size, opcode_size, 1'b0, sel_uop);

    ucontrol_store u_ucontrol_store2 (.opcode(control_store_address), .opcode_size(control_store_op_size), .control_signal(CONTROL_STORE[63:0]));
    ucontrol_store u_ucontrol_store1 (.opcode(control_store_address), .opcode_size(control_store_op_size), .control_signal(CONTROL_STORE[127:64]));

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
    or2$ or2 (ss_override, sib_seg_ovr, mod_seg_ovr);

    // SegID override for PUSH, POP - instr_seg_ovr
/*    ES = 000
    CS = 001
    SS = 010
    DS = 011
    FS = 100
    GS  = 101 */

//    segID2 = (op7 &!op6 &op5 &!op4 &!op2 &!op1);
//
//    segID1 = (!op7 &!op6 &!op5 &op4 &op2 &op1);
//
//    segID0 = (op7 &!op6 &op5 &!op4 &op3 &!op2 &!op1) | (!op7 &!op6 &!op5 &op3 &op2 &op1
//         &!op0) | (!op7 &!op6 &!op5 &op4 &op3 &op2 &op1);
//
//    push_ovr = (op7 &!op6 &op5 &!op4 &!op2 &!op1) | (!op7 &!op6 &!op5 &!op3 &op2 &op1) | (
//         !op7 &!op6 &!op5 &op3 &op2 &op1 &!op0) | (!op7 &!op6 &!op5 &op4 &op3 &op2 &op1);

    inv1$ inv1d (op7_b, opcode[7]);
    inv1$ inv2d (op6_b, opcode[6]);
    inv1$ inv3d (op5_b, opcode[5]);
    inv1$ inv4d (op4_b, opcode[4]);
    inv1$ inv5d (op3_b, opcode[3]);
    inv1$ inv6d (op2_b, opcode[2]);
    inv1$ inv7d (op1_b, opcode[1]);
    inv1$ inv8d (op0_b, opcode[0]);

    and3$ ands1 (outs1, opcode[7], op6_b, opcode[5]);
    and3$ ands2 (outs2, op4_b, op2_b, op1_b);
    and2$ ands3 (pp_ovr[2], outs1, outs2);

    and3$ ands4 (outs4, op7_b, op6_b, op5_b);
    and3$ ands5 (outs5, opcode[4], opcode[2], opcode[1]);
    and2$ ands6 (pp_ovr[1], outs4, outs5);
    
    and3$ and7 (outs7, outs1, outs2, opcode[3]);

    and3$ and8 (outs8, opcode[3], opcode[2], opcode[1]);
    and3$ and9 (outs9, outs8, outs4, op0_b);

    and3$ and10 (outs10, outs4, outs8, opcode[4]);
    or3$ ors1 (pp_ovr[0], outs9, outs7, outs10);
   
    and3$ and11 (outs11, op3_b, opcode[2], opcode[1]);
    and2$ and12 (outs12, outs4, outs11); 
    and3$ and13 (outs13, outs4, outs8, op0_b); 
    or4$ ors2 (push_pop_override, pp_ovr[2], outs10, outs12, outs13);

    mux4$ muxs1[2:0] (segID_mux1, 3'b011, 3'b010, pp_ovr, ,ss_override, push_pop_override);
    mux2$ muxs2[2:0] (DE_SEG1_ID, segID_mux1, segID, segment_override);

    // DE_BASE_REG_EN_AG=0 when mod=00 and rm=101 - disp32, base not required
    inv1$ inv3k (modrm7_b, modrm[7]);
    inv1$ inv4k (modrm6_b, modrm[6]);
    nand3$ and3k (DE_BASE_REG_EN_AG, out3p, modrm7_b, modrm6_b);

    inv1$ inv1k (segID2_b, segID[2]);
    inv1$ inv2k (segID1_b, segID[1]);

    and3$ and1k (DE_MUX_SEG_AG, segID2_b, segID1_b, segID[0]); // CS override


//module  mux2$(outb, in0, in1, s0);
   wire [1:0] mux_op_ovr_out, mux0_out, mux1_out, mux_sr1_size_out;
   wire [1:0] mux_sr2_size_out, mux_op_ovr_mem_out, mux_mem_size_out;
   wire [1:0] mux_dr1_size_out, mux_dr2_size_out;
   wire and_mux_sr1_out;

   and2$ and_mux_sr1 (and_mux_sr1_out, MOD_EQ_MEM, modrm_present);
   or2$ or_mux_sr1 (or_mux_sr1_out, and_mux_sr1_out, CS_MUX_SR1_SIZE_D2);

   mux2_2
     mux_op_ovr (.Y(mux_op_ovr_out), .IN0(2'b10), .IN1(2'b01), .S0(OPERAND_OVERRIDE_EN)), // if operand override, 16-bits; else 32-bits;
     mux0 (.Y(mux0_out), .IN0(mux_op_ovr_out), .IN1(CS_OP_SIZE_D2), .S0(CS_MUX_OP_SIZE_D2)), // if op override possible, else from control store
     mux1 (.Y(mux1_out), .IN0(mux_op_ovr_out), .IN1(CS_OP_SIZE_D2), .S0(CS_MUX_OP_SIZE_D2)), // if op override possible, else from control store
     mux_sr1_size (.Y(mux_sr1_size_out), .IN0(mux0_out), .IN1(2'b10), .S0(or_mux_sr1_out)); // if modrm possible and mod is mem OR control store wants, else other
   assign D2_SR1_SIZE_AG_OUT = mux_sr1_size_out;

   mux2_2
     mux_sr2_size (.Y(mux_sr2_size_out), .IN0(mux0_out), .IN1(CS_SR2_SIZE_D2), .S0(CS_MUX_SR2_SIZE_D2));
   assign D2_SR2_SIZE_AG_OUT = mux_sr2_size_out;

   wire or0_out;
   or2$ or0 (or0_out, CS_IS_FAR_CALL_D2, CS_IS_FAR_RET_M2);
   mux2_2
     mux_op_ovr_mem (.Y(mux_op_ovr_mem_out), .IN0(2'b11), .IN1(2'b10), .S0(OPERAND_OVERRIDE_EN)),
     mux_mem_size (.Y(mux_mem_size_out), .IN0(mux0_out), .IN1(mux_op_ovr_mem_out), .S0(or0_out));
   assign D2_MEM_SIZE_WB_OUT = mux_mem_size_out;

   mux2_2
     mux_dr1_size (.Y(mux_dr1_size_out), .IN0(mux0_out), .IN1(2'b10), .S0(CS_MUX_DR1_SIZE_D2)),
     mux_dr2_size (.Y(mux_dr2_size_out), .IN0(mux1_out), .IN1(2'b10), .S0(CS_MUX_DR2_SIZE_D2));
   assign D2_DR1_SIZE_WB_OUT = mux_dr1_size_out;
   assign D2_DR2_SIZE_WB_OUT = mux_dr2_size_out;

   mux2$
     mux_seg1_needed (.outb(D2_SEG1_NEEDED_AG), .in0(MOD_EQ_MEM), .in1(CS_SEG1_NEEDED_AG), .s0(CS_MUX_SEG1_NEEDED_AG)),
     mux_mem_rd (.outb(D2_MEM_RD_ME), .in0(MOD_EQ_MEM), .in1(CS_MEM_RD_DE), .s0(CS_MUX_MEM_RD_DE)),
     mux_mem_wr (.outb(D2_MEM_WR_ME), .in0(MOD_EQ_MEM), .in1(CS_DCACHE_WRITE_D2), .s0(CS_MUX_MEM_WR_DE));
//     mux_ld_gpr (.outb(D2_LD_GPR1_WB), .in0(MOD_EQ_REG), .in1(CS_LD_GPR1_D2), .s0(CS_MUX_LD_GPR1_D2));

   wire nand_mod_reg_out, nand_mod_mem_out;

//   nand2$ nand_mod_reg (nand_mod_reg_out, MOD_EQ_REG, modrm_present);
   nand2$ nand_mod_mem (nand_mod_mem_out, MOD_EQ_MEM, modrm_present);

//   and2$ and_mem_wr (D2_MEM_WR_ME, CS_DCACHE_WRITE_D2, nand_mod_reg_out);
   and2$ and_ld_gpr1 (D2_LD_GPR1_WB, CS_LD_GPR1_D2, nand_mod_mem_out);

   mux2_3
     mux_aluk [2:0] (.Y(D2_ALUK_EX), .IN0(IR_REG_OP), .IN1(CS_ALUK_D2), .S0(CS_MUX_ALUK_D2));
// CS_MUX_SR1_D2 == CS_MUX_SR1_AG??, CS_SR1_D2 == CS_SR1_AG??
   mux2_3
     mux_base_reg_id [2:0] (mux_base_reg_id_out, IR_MOD_RM, IR_SIB_BASE, DE_SIB_EN_AG),
     mux_sr1_id [2:0] (SR1_OUT, mux_base_reg_id_out, CS_SR1_D2, CS_MUX_SR1_D2),
     mux_sr2_id [2:0] (SR2_OUT, IR_REG_OP, CS_SR2_D2, CS_MUX_SR2_D2),
     mux_seg1_id [2:0] (SEG1_OUT, DE_SEG1_ID, 3'b000, CS_MUX_SEG1_D2), // ES segment register
     mux_seg2_id [2:0] (SEG2_OUT, 3'b010, IR_REG_OP, CS_MUX_SEG2_D2);  // SS segment register

   // LD_MM = CS_LD_MM || (MOD == 2'b11 REG && opcode == 0F7F):MOVQ mm/m64,mm  
   comp16 comp_0F7F (op_0F7F, op_0F7F_bar, opcode, 16'h0F7F);
   and2$ and_ld_mm (and_ld_mm_out, MOD_EQ_REG, op_0F7F);
   or2$ or_ld_mm (D2_LD_MM_WB, CS_LD_MM_D2, and_ld_mm_out);
 
   //CS_MM1_NEEDED_DE??, CS_SR1_NEEDED_DE?? CS_LD_MM_DE??
   // SR1_NEEDED = SR1_NEEDED || (CS_MM1_NEEDED && MOD_EQ_MEM) || (MOD_EQ_MEM && modrm_present): MM INSTs
   // and2$ and_sr1_needed (and_sr1_needed_out, CS_MM1_NEEDED_AG, MOD_EQ_MEM);
   // or3$ or_sr1_needed (D2_SR1_NEEDED_AG, CS_SR1_NEEDED_AG, and_sr1_needed_out, and_mux_sr1_out);
   or2$ or_sr1_needed (D2_SR1_NEEDED_AG, CS_SR1_NEEDED_AG, and_mux_sr1_out);

   // MM1_NEEDED = (CS_MM1_NEEDED && MOD == 11 REG && OPCODE != 0x0F7F)
   and3$ and2 (D2_MM1_NEEDED_AG, CS_MM1_NEEDED_AG, MOD_EQ_REG, op_0F7F_bar);

   comp16 comp_0FB0 (DE_CMPXCHG_AG, , {opcode[15:1], 1'b0}, 16'h0FB0); // set for cmpxchg

   wire [31:0] add_eip_out;
   wire or_exc_en_out;

   // Increment the EIP with proper length
   adder32_w_carry_in add_rel (add_eip_out, , EIP, {28'b0, instr_length_updt}, 1'b0);
   mux2_32 mux_eip_out (EIP_OUT, add_eip_out, EIP, or_exc_en_out);

   // TODO: check exception address with incremented EIP
   assign PAGE_FAULT_EXC_EXIST_OUT = PAGE_FAULT_EXC_EXIST;
   assign NMI_INT_EN_OUT = NMI_INT_EN;
   assign GEN_PROT_EXC_EN_OUT = GEN_PROT_EXC_EN;
   assign PAGE_FAULT_EXC_EN_OUT = PAGE_FAULT_EXC_EN;
 
   or3$ or_exc_en (or_exc_en_out, NMI_INT_EN, GEN_PROT_EXC_EN, PAGE_FAULT_EXC_EN);
   and2$ and_exc_v (D2_EXC_EN_V_OUT, D2_V, or_exc_en_out);

   and3$ and_uop_stall_v (D2_UOP_STALL_OUT, D2_V, CS_UOP_STALL_DE, nor_int_exist_bar);

   wire or_jmp_stall_out;
   or3$ or_jmp_stall (or_jmp_stall_out, CS_JMP_STALL_DE, CS_IS_NEAR_RET_M2, CS_IS_FAR_RET_M2);
   and2$ and_jmp_stall (D2_JMP_STALL_OUT, D2_V, or_jmp_stall_out);
   
endmodule

